"""ParlTrack Canada: Canadian parliamentary bill tracker.

Pages
  /                              the 20 most recently active bills still moving
  /passed                        the 10 most recent bills with royal assent
  /bill/<session>/<number>       "Proposed changes": a readable 1-5 paragraph summary
  /stats                         charts: bill types, sponsors' parties, Parliament clock
  /summary/<session>/<number>    JSON: official 3-sentence summary of a bill
  /api/stats/parties             JSON: progress of the party-chart job
  /debug, /healthz               troubleshooting and hosting checks

Run locally:
    pip install -r requirements.txt
    python3 app.py
"""

from __future__ import annotations

import calendar
import html as html_lib
import json
import os
import re
import threading
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime, timezone
from html.parser import HTMLParser

import requests
from flask import Flask, abort, jsonify, render_template

LEGISINFO_URL = "https://www.parl.ca/legisinfo/en/bills/json"
DOCUMENT_URL = "https://www.parl.ca/DocumentViewer/en/{session}/bill/{number}/{stage}"
LEGISINFO_HOME = "https://www.parl.ca/legisinfo/en/bills"

# Used when a bill record doesn't say which session it belongs to.
CURRENT_SESSION = os.environ.get("PARL_SESSION", "45-1")

CACHE_TTL_SECONDS = 300
TOP_ACTIVE = 20
TOP_PASSED = 10

app = Flask(__name__)

# --------------------------------------------------------------------------
# Field mapping
#
# LEGISinfo changed the shape of this feed around Aug 13, 2026
# (BillNumberFormatted -> NumberCode, CurrentStatusEn -> StatusNameEn, ...).
# Each field lists the known names for both shapes, newest first.
# If a field comes back empty, open /debug to see the real keys and add them.
# --------------------------------------------------------------------------
NUMBER_KEYS = ("NumberCode", "BillNumberFormatted")
LONG_TITLE_KEYS = ("LongTitleEn", "LongTitle", "TitleEn")
SHORT_TITLE_KEYS = ("ShortTitleEn", "ShortTitle")
STATUS_KEYS = ("StatusNameEn", "CurrentStatusEn", "StatusEn")
STAGE_KEYS = (
    "LatestCompletedMajorStageNameEn",
    "LatestCompletedMajorStageEn",
    "LatestCompletedBillStageNameEn",
)
CHAMBER_KEYS = ("OriginatingChamberNameEn", "OriginatingChamberEn")
DATE_KEYS = ("LatestActivityDateTime", "LatestCompletedBillStageDateTime")
SESSION_KEYS = ("ParlSessionCode",)

# Statuses that mean the bill is no longer moving.
INACTIVE_MARKERS = (
    "royal assent",
    "defeated",
    "withdrawn",
    "not proceeded with",
    "died on the order paper",
    "dropped",
)

# Ladder shown in the UI: (label, substrings that place a bill on that rung).
STAGES = (
    ("First reading", ("first reading",)),
    ("Second reading", ("second reading",)),
    ("Committee", ("committee",)),
    ("Report stage", ("report stage",)),
    ("Third reading", ("third reading",)),
    ("Royal assent", ("royal assent",)),
)

# Plain-language "what happens next", keyed on the status text.
NEXT_STEPS = (
    ("royal assent", "It is law. Check the bill's coming-into-force provisions for when each part takes effect."),
    ("third reading", "Final vote in this chamber; if it passes, it moves to the other chamber or to Royal Assent."),
    ("report stage", "Members consider committee amendments, then the bill goes to third reading."),
    ("committee", "Committee hears witnesses and reviews the text clause by clause, then reports back."),
    ("second reading", "Debate on the bill's principle, then a vote on whether to send it to committee."),
    ("first reading", "Formally introduced; it waits to be scheduled for second reading."),
    ("order of precedence", "A private member's bill that must be drawn for debate before it can advance."),
)

_cache: dict = {"fetched_at": 0.0, "records": None}


# --------------------------------------------------------------------------
# Fetching the bill list
# --------------------------------------------------------------------------
def _extract_records(payload) -> list[dict]:
    """The feed is either a bare list or a dict wrapping one."""
    if isinstance(payload, list):
        return [r for r in payload if isinstance(r, dict)]
    if isinstance(payload, dict):
        for key in ("Bills", "bills", "Items", "items", "Data", "data"):
            if isinstance(payload.get(key), list):
                return [r for r in payload[key] if isinstance(r, dict)]
        for value in payload.values():
            if isinstance(value, list) and value and isinstance(value[0], dict):
                return value
    return []


def fetch_records(force: bool = False) -> tuple[list[dict], str | None]:
    """Return (records, warning). Falls back to stale cache if the fetch fails."""
    now = time.time()
    fresh = _cache["records"] is not None and now - _cache["fetched_at"] < CACHE_TTL_SECONDS
    if fresh and not force:
        return _cache["records"], None

    try:
        resp = requests.get(
            LEGISINFO_URL,
            timeout=20,
            headers={"Accept": "application/json", "User-Agent": "legis-bill-tracker/1.0"},
        )
        resp.raise_for_status()
        # utf-8-sig tolerates a leading BOM, which some Parliament feeds include.
        payload = json.loads(resp.content.decode("utf-8-sig"))
        records = _extract_records(payload)
        if not records:
            raise ValueError("feed parsed but contained no bill records")
    except (requests.RequestException, ValueError) as exc:
        if _cache["records"] is not None:
            return _cache["records"], f"Could not refresh from LEGISinfo ({exc}). Showing data from the last successful fetch."
        return [], f"Could not load bills from LEGISinfo: {exc}"

    _cache.update(fetched_at=now, records=records)
    return records, None


# --------------------------------------------------------------------------
# Parsing bill records
# --------------------------------------------------------------------------
BILL_NUMBER_RE = re.compile(r"^[CS]-\d+$", re.IGNORECASE)
SESSION_RE = re.compile(r"^\d{2}-\d$")


def pick(record: dict, keys: tuple[str, ...]) -> str:
    """First non-empty string among the candidate keys."""
    for key in keys:
        value = record.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def parse_date(raw: str) -> datetime | None:
    """Parse an ISO-ish timestamp; the feed uses 0001-01-01 as 'no date'."""
    if not raw:
        return None
    try:
        parsed = datetime.fromisoformat(raw.replace("Z", "+00:00"))
    except ValueError:
        return None
    if parsed.year < 1900:
        return None
    return parsed if parsed.tzinfo else parsed.replace(tzinfo=timezone.utc)


def best_date(record: dict) -> datetime | None:
    """Prefer a field that looks like an assent date, then the usual activity dates."""
    for key, value in record.items():
        low = key.lower()
        if "assent" in low and "date" in low and isinstance(value, str):
            parsed = parse_date(value)
            if parsed:
                return parsed
    return parse_date(pick(record, DATE_KEYS))


def bill_sort_key(number: str) -> tuple[str, int]:
    match = re.match(r"([A-Za-z]+)-(\d+)", number)
    return (match.group(1).upper(), int(match.group(2))) if match else (number, 0)


def originating_chamber(number: str, raw: str) -> str:
    if raw:
        return raw
    if number.upper().startswith("C"):
        return "House of Commons"
    if number.upper().startswith("S"):
        return "Senate"
    return "Unknown"


def current_chamber(status: str, origin: str) -> str:
    low = status.lower()
    if "senate" in low and "house of commons" not in low:
        return "Senate"
    if "house of commons" in low:
        return "House of Commons"
    if "order of precedence" in low:  # private members' bills sit in the House
        return "House of Commons"
    return origin


def stage_index(status: str) -> int:
    """Rung on the ladder for this status, or -1 if it can't be placed."""
    low = status.lower()
    # Check later stages first so 'third reading' isn't caught by 'reading'.
    for idx in range(len(STAGES) - 1, -1, -1):
        if any(marker in low for marker in STAGES[idx][1]):
            return idx
    return -1


def next_step(status: str) -> str:
    low = status.lower()
    if "awaiting first reading" in low:
        return "Passed the other chamber; it now waits for first reading here."
    for marker, text in NEXT_STEPS:
        if marker in low:
            return text
    return "No further step is indicated by the current status."


def is_active(status: str) -> bool:
    low = status.lower()
    return bool(status) and not any(marker in low for marker in INACTIVE_MARKERS)


def is_passed(status: str) -> bool:
    return "royal assent" in status.lower()


def build_breakdown(number: str, short: str, long: str, origin: str, current: str,
                    status: str, stage: str, passed: bool) -> list[dict]:
    """Exactly five labelled lines per bill, built from the feed's own fields."""
    if passed:
        where = f"Introduced in the {origin}; passed by both chambers."
    elif current != origin:
        where = f"Introduced in the {origin}; currently in the {current}."
    else:
        where = f"Introduced in the {origin} and still there."
    status_line = status if not stage else f"{status}. Last major stage completed: {stage}."
    return [
        {"label": "Bill", "text": f"{number}" + (f", {short}" if short else "")},
        {"label": "Purpose", "text": long or "No title available."},
        {"label": "Chamber", "text": where},
        {"label": "Status", "text": status_line},
        {"label": "Next", "text": next_step(status)},
    ]


def normalize(record: dict) -> dict | None:
    number = pick(record, NUMBER_KEYS)
    status = pick(record, STATUS_KEYS)
    if not number:
        return None
    short = pick(record, SHORT_TITLE_KEYS)
    long = pick(record, LONG_TITLE_KEYS)
    stage = pick(record, STAGE_KEYS)
    origin = originating_chamber(number, pick(record, CHAMBER_KEYS))
    current = current_chamber(status, origin)
    passed = is_passed(status)
    session = pick(record, SESSION_KEYS)
    if not SESSION_RE.match(session):
        parl, sess = record.get("ParliamentNumber"), record.get("SessionNumber")
        session = f"{parl}-{sess}" if isinstance(parl, int) and isinstance(sess, int) else CURRENT_SESSION
        if not SESSION_RE.match(session):
            session = CURRENT_SESSION
    number_ok = bool(BILL_NUMBER_RE.match(number))
    return {
        "number": number,
        "short_title": short,
        "title": long,
        "status": status,
        "chamber": origin,
        "current_chamber": current,
        "chamber_class": "senate" if current == "Senate" else "house",
        "stage_index": stage_index(status),
        "passed": passed,
        "session": session,
        "number_ok": number_ok,
        "doc_url": (DOCUMENT_URL.format(session=session, number=number.upper(), stage="first-reading")
                    if number_ok else LEGISINFO_HOME),
        "active_date": parse_date(pick(record, DATE_KEYS)),
        "sort_date": best_date(record),
        "breakdown": build_breakdown(number, short, long, origin, current, status, stage, passed),
    }


def top_active_bills(records: list[dict], limit: int = TOP_ACTIVE) -> list[dict]:
    bills = [b for b in (normalize(r) for r in records) if b and is_active(b["status"])]

    # Stable sorts, least significant key first:
    #   bill number -> furthest along its path -> most recent activity.
    # Dated bills outrank undated ones, because the feed leaves dates blank
    # on some records.
    bills.sort(key=lambda b: bill_sort_key(b["number"]))
    bills.sort(key=lambda b: b["stage_index"], reverse=True)
    epoch = datetime.min.replace(tzinfo=timezone.utc)
    bills.sort(key=lambda b: b["active_date"] or epoch, reverse=True)
    return bills[:limit]


def recent_passed_bills(records: list[dict], limit: int = TOP_PASSED) -> tuple[list[dict], bool]:
    """Newest royal assents first. Returns (bills, order_is_approximate)."""
    bills = [b for b in (normalize(r) for r in records) if b and b["passed"]]
    epoch = datetime.min.replace(tzinfo=timezone.utc)
    bills.sort(key=lambda b: bill_sort_key(b["number"]), reverse=True)  # fallback order
    bills.sort(key=lambda b: b["sort_date"] or epoch, reverse=True)
    top = bills[:limit]
    approximate = any(b["sort_date"] is None for b in top)
    return top, approximate


# --------------------------------------------------------------------------
# Official bill summaries
#
# Every bill printed by Parliament opens with a "Summary" section written by
# the drafters. We read it from the bill's text page, keep the first three
# sentences, and cache the result. Summaries load after the page does (see the
# script in base.html), so a slow Parliament page never blocks the bill list.
# --------------------------------------------------------------------------
SUMMARY_TTL = 24 * 3600
SUMMARY_FAIL_TTL = 15 * 60
SUMMARY_MAX_BYTES = 3_000_000
SUMMARY_MAX_SENTENCES = 3
SUMMARY_MAX_CHARS = 520
SUMMARY_STAGES = ("first-reading", "royal-assent")

_summary_cache: dict = {}
_summary_lock = threading.Lock()


class _TextExtractor(HTMLParser):
    """Collects visible text; adds a space at every tag so words never fuse."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts: list[str] = []
        self._skip = 0

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style"):
            self._skip += 1
        self.parts.append(" ")

    def handle_endtag(self, tag):
        if tag in ("script", "style") and self._skip:
            self._skip -= 1
        self.parts.append(" ")

    def handle_data(self, data):
        if not self._skip:
            self.parts.append(data)


def html_to_text(raw_html: str) -> str:
    parser = _TextExtractor()
    try:
        parser.feed(raw_html)
        parser.close()
    except Exception:  # truncated or malformed HTML: use what we have
        pass
    text = "".join(parser.parts)
    text = re.sub(r"[\u200b-\u200f\u2060\ufeff]", "", text)  # invisible characters in legal text
    return re.sub(r"\s+", " ", text).strip()


def extract_summary(text: str) -> str | None:
    """Pull the text of the SUMMARY section out of a bill page's text."""
    end = re.search(r"Available on the [A-Za-z .]{0,60}website", text)
    if not end:
        return None
    start = text.rfind("SUMMARY", 0, end.start())
    if start == -1:
        return None
    body = text[start + len("SUMMARY"):end.start()].strip()
    # If the 'summary' swallowed the page's navigation, the bill has no summary.
    if not body or "TABLE OF PROVISIONS" in body:
        return None
    return body


def condense(body: str, max_sentences: int = SUMMARY_MAX_SENTENCES,
             max_chars: int = SUMMARY_MAX_CHARS) -> str:
    """First few sentences, trimmed at a natural break if they run long."""
    sentences = re.split(r"(?<=[.!?])\s+(?=[A-Z(\u201c\"])", body.strip())
    out = " ".join(sentences[:max_sentences]).strip()
    if len(out) <= max_chars:
        return out
    cut = out[:max_chars]
    semi = cut.rfind("; ")
    cut = cut[:semi] if semi > max_chars * 0.4 else cut[:cut.rfind(" ")]
    return cut.rstrip(" ,;:(") + "\u2026"


def _download_text(url: str) -> str | None:
    """Download a bill page, stopping early once the summary has been passed."""
    try:
        with requests.get(url, timeout=20, stream=True,
                          headers={"User-Agent": "legis-bill-tracker/1.0"}) as resp:
            if resp.status_code != 200:
                return None
            buf = b""
            for chunk in resp.iter_content(chunk_size=65536):
                buf += chunk
                if b"Available on the" in buf or len(buf) >= SUMMARY_MAX_BYTES:
                    break
    except requests.RequestException:
        return None
    return html_to_text(buf.decode("utf-8", errors="replace"))


def get_summary_body(parl_session: str, number: str) -> str | None:
    """The bill's full SUMMARY section (cached). The card shows a short cut of it;
    the detail page builds its paragraphs from the whole thing."""
    key = (parl_session, number)
    now = time.time()
    with _summary_lock:
        hit = _summary_cache.get(key)
    if hit and now < hit["expires"]:
        return hit["body"]

    body = None
    for stage in SUMMARY_STAGES:
        text = _download_text(DOCUMENT_URL.format(session=parl_session, number=number, stage=stage))
        body = extract_summary(text) if text else None
        if body:
            break

    ttl = SUMMARY_TTL if body else SUMMARY_FAIL_TTL
    with _summary_lock:
        _summary_cache[key] = {"body": body, "expires": now + ttl}
    return body


def get_summary(parl_session: str, number: str) -> str | None:
    body = get_summary_body(parl_session, number)
    return condense(body) if body else None


# --------------------------------------------------------------------------
# Per-bill data (sponsor, Library of Parliament summary)
#
# The list feed leaves sponsors and summaries blank, but each bill has its own
# JSON page. We keep only the few fields we need, because a bill with many
# speeches can be megabytes and the free hosting plan has little memory.
# --------------------------------------------------------------------------
BILL_JSON_URL = "https://www.parl.ca/legisinfo/en/bill/{session}/{number}/json"
BILL_JSON_TTL = 6 * 3600
BILL_JSON_FAIL_TTL = 5 * 60
LEGISINFO_BILL_URL = "https://www.parl.ca/legisinfo/en/bill/{session}/{number}"

_bill_json_cache: dict = {}
_bill_json_lock = threading.Lock()


def _find_caucus(node, person_id) -> str | None:
    """Search a bill's JSON for a speech by this person; return their caucus then."""
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, dict):
            if cur.get("PersonId") == person_id and isinstance(cur.get("CaucusShortNameEn"), str) \
                    and cur["CaucusShortNameEn"].strip():
                return cur["CaucusShortNameEn"].strip()
            stack.extend(v for v in cur.values() if isinstance(v, (dict, list)))
        elif isinstance(cur, list):
            stack.extend(v for v in cur if isinstance(v, (dict, list)))
    return None


def fetch_bill_json(parl_session: str, number: str) -> dict | None:
    """Slimmed per-bill data, or None if Parliament's page couldn't be read."""
    key = (parl_session, number.upper())
    now = time.time()
    with _bill_json_lock:
        hit = _bill_json_cache.get(key)
    if hit and now < hit["expires"]:
        return hit["data"]

    data = None
    try:
        resp = requests.get(
            BILL_JSON_URL.format(session=parl_session, number=number.lower()),
            timeout=25,
            headers={"Accept": "application/json", "User-Agent": "legis-bill-tracker/1.0"},
        )
        resp.raise_for_status()
        payload = json.loads(resp.content.decode("utf-8-sig"))
        raw = payload[0] if isinstance(payload, list) and payload else payload
        if isinstance(raw, dict):
            sponsor_id = raw.get("SponsorPersonId")
            sponsor_id = sponsor_id if isinstance(sponsor_id, int) and sponsor_id > 0 else None
            data = {
                "sponsor_id": sponsor_id,
                "sponsor_name": (raw.get("SponsorPersonName") or "").strip(),
                "sponsor_title": (raw.get("SponsorAffiliationTitleEn") or "").strip(),
                "sponsor_riding": (raw.get("SponsorConstituencyNameEn") or "").strip(),
                "doc_type": (raw.get("BillDocumentTypeNameEn") or "").strip(),
                "long_title": (raw.get("LongTitleEn") or "").strip(),
                "summary_html": raw.get("ShortLegislativeSummaryEn") or "",
                "sponsor_caucus": _find_caucus(raw, sponsor_id) if sponsor_id else None,
            }
    except (requests.RequestException, ValueError, IndexError):
        data = None

    ttl = BILL_JSON_TTL if data else BILL_JSON_FAIL_TTL
    with _bill_json_lock:
        _bill_json_cache[key] = {"data": data, "expires": now + ttl}
    return data


# --------------------------------------------------------------------------
# "Proposed changes" detail page: turn a summary into 1 to 5 readable paragraphs
# --------------------------------------------------------------------------
MAX_PARAGRAPHS = 5
PARAGRAPH_CHARS = 850
ITEM_CHARS = 420
SENTENCE_SPLIT = re.compile(r"(?<=[.!?])\s+(?=[A-Z(“\"])")
LIST_MARKER = re.compile(r"^\(\s*[A-Za-z0-9]{1,4}\s*\)\s*")
BOILERPLATE = re.compile(
    r"legislative summary is currently being prepared|following executive summary is available",
    re.IGNORECASE,
)
PART_LEAD = re.compile(r"^((?:Part|Division) \d+[A-Za-z]?)\b\s*,?\s*")


def trim_text(text: str, limit: int) -> str:
    """Shorten at a sentence end if possible, else a semicolon, else a word."""
    if len(text) <= limit:
        return text
    cut = text[:limit]
    period = max(cut.rfind(". "), cut.rfind(".” "))
    if period > limit * 0.5:
        return cut[:period + 1]
    semi = cut.rfind("; ")
    if semi > limit * 0.5:
        return cut[:semi].rstrip(" ,;:") + "…"
    return cut[:cut.rfind(" ")].rstrip(" ,;:(") + "…"


def blocks_from_legisinfo(raw_html: str) -> tuple[list[dict], bool]:
    """Library of Parliament summary (HTML with <br/> breaks) -> paragraph blocks.

    A block is {"lead": str|None, "text": str, "points": [str]}; "(a)", "(b)" lines
    become the points of the paragraph above them.
    """
    if not raw_html:
        return [], False
    text = re.sub(r"(?i)<\s*(br\s*/?|/p|/div|/li)\s*>", "\n", raw_html)
    text = re.sub(r"(?i)<\s*li[^>]*>", "\n", text)
    text = html_lib.unescape(re.sub(r"<[^>]+>", " ", text))
    text = re.sub(r"[​-‏⁠﻿]", "", text)
    lines = [re.sub(r"[ \t ]+", " ", ln).strip() for ln in text.split("\n")]
    lines = [ln for ln in lines if ln and not BOILERPLATE.search(ln)]

    blocks: list[dict] = []
    for ln in lines:
        if LIST_MARKER.match(ln):
            item = trim_text(LIST_MARKER.sub("", ln), ITEM_CHARS)
            if not blocks:
                blocks.append({"lead": None, "text": "", "points": []})
            blocks[-1]["points"].append(item)
        else:
            blocks.append({"lead": None, "text": trim_text(ln, PARAGRAPH_CHARS), "points": []})

    truncated = len(blocks) > MAX_PARAGRAPHS
    return blocks[:MAX_PARAGRAPHS], truncated


def blocks_from_bill_text(body: str) -> tuple[list[dict], bool]:
    """The bill's own SUMMARY text -> paragraph blocks.

    Drafters usually write "Part 1 amends ... Part 2 enacts ..."; each Part becomes a
    paragraph. Without Parts, sentences are grouped three at a time.
    """
    sentences = [s.strip() for s in SENTENCE_SPLIT.split(body.strip()) if s.strip()]
    if not sentences:
        return [], False

    groups: list[list[str]] = []
    for sent in sentences:
        if not groups or PART_LEAD.match(sent):
            groups.append([sent])
        elif PART_LEAD.match(groups[-1][0]):
            groups[-1].append(sent)          # a Part keeps going until the next Part
        elif len(groups[-1]) >= 3:
            groups.append([sent])
        else:
            groups[-1].append(sent)

    blocks = []
    for group in groups:
        joined = " ".join(group)
        lead = None
        match = PART_LEAD.match(joined)
        if match:
            lead = match.group(1)
            joined = joined[match.end():]
        blocks.append({"lead": lead, "text": trim_text(joined, PARAGRAPH_CHARS), "points": []})

    truncated = len(blocks) > MAX_PARAGRAPHS
    return blocks[:MAX_PARAGRAPHS], truncated


def find_bill(records: list[dict], parl_session: str, number: str) -> dict | None:
    for rec in records:
        bill = normalize(rec)
        if bill and bill["number"].upper() == number.upper() and bill["session"] == parl_session:
            return bill
    return None


# --------------------------------------------------------------------------
# Statistics
# --------------------------------------------------------------------------
# Update these two dates after the next federal election.
PARLIAMENT_NUMBER = 45
PARLIAMENT_OPENED = date(2025, 5, 26)     # first sitting day of the 45th Parliament
SCHEDULED_ELECTION = date(2029, 10, 15)   # fixed-date election: 3rd Monday of October

PMB_LABEL = "Private members' bills"
GOV_LABEL = "Government bills (House)"
SEN_PUBLIC_LABEL = "Senate public bills"
SEN_GOV_LABEL = "Senate government bills"

TYPE_COLOURS = {
    GOV_LABEL: "#2b2d31",
    PMB_LABEL: "#d52b1e",
    SEN_PUBLIC_LABEL: "#74777f",
    SEN_GOV_LABEL: "#a9acb3",
}
OTHER_COLOUR = "#d6d7da"

PARTY_COLOURS = {
    "Liberal": "#d71920",
    "Conservative": "#1a4782",
    "NDP": "#f37021",
    "Bloc Québécois": "#33b2cc",
    "Green Party": "#3d9b35",
    "Independent": "#8a8d93",
    "Unknown": "#d6d7da",
}

MEMBERS_URL = "https://www.ourcommons.ca/members/en/search"
MEMBERS_TTL = 12 * 3600
MEMBER_LINK_RE = re.compile(r"/Members/en/[^\"'<>\s()]*\((\d+)\)", re.IGNORECASE)
PARTY_RE = re.compile(
    r"Bloc Qu[eé]b[eé]cois|Conservative|Green Party|Liberal|New Democratic|NDP|Independent",
    re.IGNORECASE,
)

_members_cache: dict = {"expires": 0.0, "parties": {}}
_members_lock = threading.Lock()


def canon_party(text: str) -> str | None:
    match = PARTY_RE.search(text or "")
    if not match:
        return None
    low = match.group(0).lower()
    if low.startswith("bloc"):
        return "Bloc Québécois"
    if low.startswith("conservative"):
        return "Conservative"
    if low.startswith("green"):
        return "Green Party"
    if low.startswith("liberal"):
        return "Liberal"
    if low.startswith("independent"):
        return "Independent"
    return "NDP"


def parse_member_parties(page_html: str) -> dict[int, str]:
    """{PersonId: party} from the House of Commons member search page."""
    matches = list(MEMBER_LINK_RE.finditer(page_html))
    gathered: dict[int, str] = {}
    for i, match in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(page_html)
        chunk = html_to_text(page_html[match.end():min(end, match.end() + 3000)])[:600]
        pid = int(match.group(1))
        gathered[pid] = gathered.get(pid, "") + " " + chunk
    parties = {}
    for pid, chunk in gathered.items():
        party = canon_party(chunk)
        if party:
            parties[pid] = party
    return parties


def get_member_parties() -> dict[int, str]:
    """Current party of every sitting MP, keyed by PersonId. {} if it can't be read."""
    now = time.time()
    with _members_lock:
        if now < _members_cache["expires"]:
            return _members_cache["parties"]
    parties: dict[int, str] = {}
    try:
        resp = requests.get(MEMBERS_URL, timeout=25, headers={"User-Agent": "legis-bill-tracker/1.0"})
        resp.raise_for_status()
        parties = parse_member_parties(resp.text)
    except requests.RequestException:
        parties = {}
    if len(parties) < 100:  # a real parse finds about 340; fewer means the page changed
        parties = {}
    with _members_lock:
        _members_cache.update(parties=parties, expires=now + (MEMBERS_TTL if parties else 300))
    return parties


def is_pro_forma(record: dict) -> bool:
    return bool(record.get("IsProForma")) or "pro forma" in pick(record, STATUS_KEYS).lower()


def is_house_origin(record: dict, number: str) -> bool:
    org = record.get("OriginatingChamberOrganizationId")
    if org in (1, 2):
        return org == 1
    return number.upper().startswith("C")


def bill_type_label(record: dict, number: str) -> str:
    raw = (record.get("BillDocumentTypeNameEn") or "").strip()
    low = raw.lower()
    if "private member" in low:
        return PMB_LABEL
    if "senate" in low and "government" in low:
        return SEN_GOV_LABEL
    if "senate" in low:
        return SEN_PUBLIC_LABEL
    if "government" in low:
        return GOV_LABEL
    if raw:
        return raw
    # Feed gave no type: infer from the flags and bill number.
    if not is_house_origin(record, number):
        return SEN_GOV_LABEL if record.get("IsGovernmentBill") else SEN_PUBLIC_LABEL
    return GOV_LABEL if record.get("IsGovernmentBill") else PMB_LABEL


def status_group(status: str) -> str:
    low = status.lower()
    if "royal assent" in low:
        return "Became law"
    if not is_active(status):
        return "Defeated or ended"
    if "order of precedence" in low:
        return "Private members' bills awaiting a draw"
    if current_chamber(status, "House of Commons") == "Senate":
        return "In the Senate"
    return "In the House of Commons"


GROUP_ORDER = ("Became law", "In the House of Commons", "In the Senate",
               "Private members' bills awaiting a draw", "Defeated or ended")


def stats_rows(records: list[dict]) -> list[dict]:
    rows = []
    for rec in records:
        number = pick(rec, NUMBER_KEYS)
        if not number or is_pro_forma(rec):
            continue
        status = pick(rec, STATUS_KEYS)
        rows.append({
            "number": number,
            "type": bill_type_label(rec, number),
            "group": status_group(status),
            "house": is_house_origin(rec, number),
        })
    return rows


def make_donut(items: list[tuple[str, int, str]]) -> dict | None:
    """Server-side donut: a CSS conic-gradient plus a legend with counts and percents."""
    items = [(label, count, colour) for label, count, colour in items if count > 0]
    total = sum(count for _, count, _ in items)
    if not total:
        return None
    stops, legend, running = [], [], 0
    for label, count, colour in items:
        start = running / total * 100
        running += count
        stops.append(f"{colour} {start:.3f}% {running / total * 100:.3f}%")
        pct = count / total * 100
        legend.append({"label": label, "count": count, "colour": colour,
                       "pct": "<1" if pct < 1 else f"{pct:.0f}"})
    return {"total": total, "gradient": "conic-gradient(" + ", ".join(stops) + ")", "legend": legend}


def type_donut(rows: list[dict]) -> dict | None:
    counts = Counter(r["type"] for r in rows)
    ordered = [GOV_LABEL, PMB_LABEL, SEN_PUBLIC_LABEL, SEN_GOV_LABEL]
    ordered += sorted(k for k in counts if k not in ordered)
    return make_donut([(k, counts[k], TYPE_COLOURS.get(k, OTHER_COLOUR)) for k in ordered])


def party_donut(rows: list[dict]) -> dict | None:
    counts = Counter(r["party"] for r in rows)
    known = sorted((p for p in counts if p != "Unknown"), key=lambda p: -counts[p])
    order = known + (["Unknown"] if "Unknown" in counts else [])
    return make_donut([(p, counts[p], PARTY_COLOURS.get(p, OTHER_COLOUR)) for p in order])


def outcome_table(rows: list[dict]) -> list[dict]:
    """Per bill type: how many became law, ended, or are still alive."""
    table = []
    for label in dict.fromkeys(r["type"] for r in rows):
        mine = [r for r in rows if r["type"] == label]
        law = sum(r["group"] == "Became law" for r in mine)
        ended = sum(r["group"] == "Defeated or ended" for r in mine)
        table.append({"label": label, "total": len(mine), "law": law, "ended": ended,
                      "alive": len(mine) - law - ended,
                      "law_pct": f"{law / len(mine) * 100:.0f}" if mine else "0"})
    table.sort(key=lambda t: -t["total"])
    return table


def stage_bars(rows: list[dict]) -> list[dict]:
    counts = Counter(r["group"] for r in rows)
    biggest = max(counts.values(), default=1)
    return [{"label": g, "count": counts[g], "width": round(counts[g] / biggest * 100)}
            for g in GROUP_ORDER if counts.get(g)]


def _years_months_days(a: date, b: date) -> tuple[int, int, int]:
    years, months, days = b.year - a.year, b.month - a.month, b.day - a.day
    if days < 0:
        months -= 1
        prev_month = b.month - 1 or 12
        prev_year = b.year if b.month > 1 else b.year - 1
        days += calendar.monthrange(prev_year, prev_month)[1]
    if months < 0:
        years -= 1
        months += 12
    return years, months, days


def _plural(n: int, word: str) -> str:
    return f"{n} {word}" + ("" if n == 1 else "s")


def _span_text(y: int, m: int, d: int) -> str:
    parts = [_plural(y, "year")] if y else []
    if m:
        parts.append(_plural(m, "month"))
    if d or not parts:
        parts.append(_plural(d, "day"))
    return ", ".join(parts[:-1]) + " and " + parts[-1] if len(parts) > 1 else parts[0]


def _ordinal(n: int) -> str:
    suffix = "th" if 10 <= n % 100 <= 20 else {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
    return f"{n}{suffix}"


def parliament_clock(today: date | None = None) -> dict:
    today = today or date.today()
    total_days = (SCHEDULED_ELECTION - PARLIAMENT_OPENED).days
    elapsed_days = max((today - PARLIAMENT_OPENED).days, 0)
    remaining_days = (SCHEDULED_ELECTION - today).days
    pct = min(max(elapsed_days / total_days * 100, 0), 100) if total_days > 0 else 0
    sess = CURRENT_SESSION.split("-")[-1]
    return {
        "parliament": _ordinal(PARLIAMENT_NUMBER),
        "session": _ordinal(int(sess)) if sess.isdigit() else "",
        "opened": PARLIAMENT_OPENED,
        "election": SCHEDULED_ELECTION,
        "elapsed_text": _span_text(*_years_months_days(PARLIAMENT_OPENED, max(today, PARLIAMENT_OPENED))),
        "elapsed_days": elapsed_days,
        "remaining_days": remaining_days,
        "remaining_text": _span_text(*_years_months_days(today, SCHEDULED_ELECTION)) if remaining_days > 0 else "",
        "pct": round(pct, 1),
        "pct_label": f"{pct:.0f}",
        "overdue": remaining_days <= 0,
    }


# ---- Party chart: a background job, because it needs one request per House bill ----
PARTY_TTL = 12 * 3600
PARTY_RETRY_AFTER = 10 * 60
PARTY_WORKERS = 6

_party_state: dict = {"status": "idle", "done": 0, "total": 0, "data": None, "finished": 0.0, "error": None}
_party_lock = threading.Lock()


def party_snapshot() -> dict:
    with _party_lock:
        return dict(_party_state)


def ensure_party_job(records: list[dict]) -> None:
    """Start the job unless one is running or the cached result is still fresh."""
    now = time.time()
    with _party_lock:
        if _party_state["status"] == "running":
            return
        if _party_state["data"] is not None and now - _party_state["finished"] < PARTY_TTL:
            return
        if _party_state["status"] == "error" and now - _party_state["finished"] < PARTY_RETRY_AFTER:
            return
        _party_state.update(status="running", done=0, total=0, error=None)
    threading.Thread(target=_run_party_job, args=(records,), daemon=True).start()


def _run_party_job(records: list[dict]) -> None:
    try:
        house, senate_count = [], 0
        for rec in records:
            number = pick(rec, NUMBER_KEYS)
            if not BILL_NUMBER_RE.match(number) or is_pro_forma(rec):
                continue
            if is_house_origin(rec, number):
                session = normalize(rec)["session"]
                house.append((number, session, bill_type_label(rec, number)))
            else:
                senate_count += 1
        with _party_lock:
            _party_state["total"] = len(house)

        members = get_member_parties()

        def work(item):
            number, session, type_label = item
            info = fetch_bill_json(session, number)
            party = None
            if info:
                if info["sponsor_id"] in members:
                    party = members[info["sponsor_id"]]
                elif info["sponsor_caucus"]:
                    party = canon_party(info["sponsor_caucus"])
            return {"number": number, "type": type_label, "party": party or "Unknown", "ok": info is not None}

        results = []
        with ThreadPoolExecutor(max_workers=PARTY_WORKERS) as pool:
            futures = [pool.submit(work, item) for item in house]
            for fut in as_completed(futures):
                results.append(fut.result())
                with _party_lock:
                    _party_state["done"] = len(results)

        failed = sum(not r["ok"] for r in results)
        if house and failed > len(house) * 0.3:
            raise RuntimeError(f"Parliament's site did not answer for {failed} of {len(house)} bills")

        data = {"rows": results, "senate_count": senate_count, "members_found": bool(members)}
        with _party_lock:
            _party_state.update(status="done", data=data, finished=time.time(), error=None)
    except Exception as exc:  # any failure must leave the page usable
        with _party_lock:
            _party_state.update(status="error", finished=time.time(), error=str(exc))


# --------------------------------------------------------------------------
# Routes
# --------------------------------------------------------------------------
def _fetched_at():
    return datetime.fromtimestamp(_cache["fetched_at"]) if _cache["fetched_at"] else None


@app.route("/")
def index():
    records, warning = fetch_records()
    bills = top_active_bills(records)
    if records and not bills and not warning:
        warning = ("The feed loaded, but no bills could be read from it. LEGISinfo may have "
                   "renamed its fields; open /debug to see the keys it returns.")
    return render_template(
        "index.html",
        active_tab="active",
        bills=bills,
        stages=[label for label, _ in STAGES],
        warning=warning,
        total=len(records),
        fetched_at=_fetched_at(),
    )


@app.route("/passed")
def passed():
    records, warning = fetch_records()
    bills, approximate = recent_passed_bills(records)
    return render_template(
        "passed.html",
        active_tab="passed",
        bills=bills,
        approximate=approximate,
        stages=[label for label, _ in STAGES],
        warning=warning,
        total=len(records),
        fetched_at=_fetched_at(),
    )


@app.route("/summary/<parl_session>/<number>")
def summary(parl_session: str, number: str):
    # Only well-formed values reach the outbound request.
    if not SESSION_RE.match(parl_session) or not BILL_NUMBER_RE.match(number):
        abort(404)
    number = number.upper()
    text = get_summary(parl_session, number)
    response = jsonify(
        summary=text,
        url=DOCUMENT_URL.format(session=parl_session, number=number, stage="first-reading"),
    )
    response.headers["Cache-Control"] = "public, max-age=3600" if text else "public, max-age=300"
    return response


@app.route("/bill/<parl_session>/<number>")
def bill_detail(parl_session: str, number: str):
    if not SESSION_RE.match(parl_session) or not BILL_NUMBER_RE.match(number):
        abort(404)
    number = number.upper()
    records, warning = fetch_records()
    bill = find_bill(records, parl_session, number)
    info = fetch_bill_json(parl_session, number)

    blocks, truncated, source = [], False, ""
    if info and info["summary_html"]:
        blocks, truncated = blocks_from_legisinfo(info["summary_html"])
        source = "Summary by the Library of Parliament, published on LEGISinfo."
    if not blocks:
        body = get_summary_body(parl_session, number)
        if body:
            blocks, truncated = blocks_from_bill_text(body)
            source = "Summary printed at the start of the bill by its drafters."

    sponsor = None
    if info and info["sponsor_name"]:
        sponsor = {"name": info["sponsor_name"], "title": info["sponsor_title"], "riding": info["sponsor_riding"]}

    return render_template(
        "bill.html",
        active_tab=None,
        number=number,
        bill=bill,
        title=(bill and bill["title"]) or (info and info["long_title"]) or "",
        short_title=(bill and bill["short_title"]) or "",
        doc_type=(info and info["doc_type"]) or "",
        sponsor=sponsor,
        blocks=blocks,
        truncated=truncated,
        source=source,
        doc_url=DOCUMENT_URL.format(session=parl_session, number=number, stage="first-reading"),
        legis_url=LEGISINFO_BILL_URL.format(session=parl_session, number=number.lower()),
        warning=warning if not bill else None,
        fetched_at=_fetched_at(),
        total=len(records),
    )


@app.route("/stats")
def stats():
    records, warning = fetch_records()
    if records:
        ensure_party_job(records)
    rows = stats_rows(records)
    snap = party_snapshot()

    party = None
    if snap["data"] is not None:
        prows = snap["data"]["rows"]
        party = {
            "all": party_donut(prows),
            "pmb": party_donut([r for r in prows if r["type"] == PMB_LABEL]),
            "senate_count": snap["data"]["senate_count"],
            "unknown": sum(r["party"] == "Unknown" for r in prows),
            "members_found": snap["data"]["members_found"],
            "updated": datetime.fromtimestamp(snap["finished"]),
        }

    return render_template(
        "stats.html",
        active_tab="stats",
        clock=parliament_clock(),
        types=type_donut(rows),
        stage_bars=stage_bars(rows),
        outcomes=outcome_table(rows),
        bill_total=len(rows),
        party=party,
        party_status=snap["status"],
        party_error=snap["error"],
        party_progress=(snap["done"], snap["total"]),
        warning=warning,
        fetched_at=_fetched_at(),
        total=len(records),
    )


@app.route("/api/stats/parties")
def stats_parties_api():
    """Polled by the Statistics page while the party chart is being built."""
    records, _ = fetch_records()
    if records:
        ensure_party_job(records)
    snap = party_snapshot()
    response = jsonify(status=snap["status"], done=snap["done"], total=snap["total"],
                       ready=snap["data"] is not None, error=snap["error"])
    response.headers["Cache-Control"] = "no-store"
    return response


@app.route("/debug")
def debug():
    """Show the raw keys and first record, for adapting to schema changes."""
    # Only bypass the cache when running locally in debug mode, so a public
    # deployment can't be used to hammer LEGISinfo.
    records, warning = fetch_records(force=app.debug)
    keys = sorted(records[0].keys()) if records else []
    statuses = Counter(pick(r, STATUS_KEYS) or "(none)" for r in records)
    return jsonify(
        warning=warning,
        record_count=len(records),
        keys=keys,
        date_like_keys=[k for k in keys if "date" in k.lower()],
        summary_like_keys=[k for k in keys if "summary" in k.lower()],
        status_counts=statuses.most_common(15),
        first_record=records[0] if records else None,
    )


@app.route("/healthz")
def healthz():
    """Lightweight check for the hosting platform; makes no outside requests."""
    return "ok", 200


if __name__ == "__main__":
    # Local use: python3 app.py   (set FLASK_DEBUG=1 for auto-reload and verbose errors).
    # Hosted use goes through gunicorn (see gunicorn.conf.py) and never reaches this block.
    app.run(debug=os.environ.get("FLASK_DEBUG") == "1", port=int(os.environ.get("PORT", 5000)))
