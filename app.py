"""ParlTrack Canada: Canadian parliamentary bill tracker.

Pages
  /                              the 20 most recently active bills still moving
  /passed                        the 10 most recent bills with royal assent
  /bill/<session>/<number>       "Proposed changes": a readable 1-5 paragraph summary
  /members                       directory of every sitting MP, by party, with photos and contacts
  /compare                       two bills side by side
  /glossary                      plain-language definitions
  /export/*.csv                  spreadsheet downloads of the lists
  /following                     the bills you've starred (stored in your browser)
  /api/bill/<session>/<number>   JSON: sponsor, party, votes for one bill
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
import gzip
import csv
import io
import unicodedata
import xml.etree.ElementTree as ET
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
from flask import Flask, Response, abort, jsonify, render_template, request, url_for

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


def record_dates(record: dict) -> dict[str, datetime]:
    """Every real timestamp on a feed record, by field name."""
    out = {}
    for key, value in record.items():
        if "DateTime" in key and isinstance(value, str):
            parsed = parse_date(value)
            if parsed:
                out[key] = parsed
    return out


AMEND_SPLIT = re.compile(r"\s*\(|,? and (?:to |make |other |consequential)|,? to |;")
AMEND_PARTS = re.compile(r",(?!\s*\d)\s*(?:and\s+)?(?:the\s+)?| and (?:the )?")

TOPICS = (
    ("Justice and policing", ("criminal", "justice", "police", "sentenc", "bail", "firearm", "offence", "victim", "court", "corrections", "judges")),
    ("Immigration and citizenship", ("immigration", "citizenship", "refugee", "border", "asylum")),
    ("Health and safety", ("health", "drug", "medical", "pharma", "cannabis", "tobacco", "food and drugs", "mental")),
    ("Housing and cost of living", ("housing", "rent", "mortgage", "home ", "homes", "grocery", "price")),
    ("Money and taxes", ("tax", "budget", "income", "financ", "bank", "economic statement", "fiscal", "payment", "pension", "insurance", "affordab")),
    ("Environment and energy", ("environment", "climate", "energy", "emission", "pipeline", "carbon", "oil", "fisher", "wildlife", "water")),
    ("Elections and democracy", ("election", "elector", "parliament", "senate", "ethics", "lobby", "representation", "constitution")),
    ("Defence and security", ("defence", "security", "military", "armed forces", "foreign", "sanction", "intelligence", "terror")),
    ("Indigenous affairs", ("indigenous", "first nations", "inuit", "m\u00e9tis", "metis", "reconciliation")),
    ("Work and business", ("labour", "employment", "worker", "business", "competition", "trade", "union", "wage")),
    ("Transport and infrastructure", ("transport", "rail", "airline", "port", "marine", "infrastructure", "highway", "shipping")),
    ("Technology and media", ("online", "internet", "digital", "privacy", "data", "broadcast", "artificial", "cyber", "copyright")),
    ("Agriculture and food", ("agricultur", "farm", "supply management", "dairy", "grain")),
)


def topic_for(text: str) -> str:
    low = text.lower()
    for label, words in TOPICS:
        if any(w in low for w in words):
            return label
    return "Other"


def amended_acts(title: str) -> list[str]:
    """Acts named after 'An Act to amend ...' in a long title (best effort)."""
    match = re.search(r"\bto amend (?:the )?(.+)", title, re.IGNORECASE)
    if not match:
        return []
    rest = AMEND_SPLIT.split(match.group(1))[0]
    acts = [p.strip(" .") for p in AMEND_PARTS.split(rest) if p.strip(" .")]
    return [a for a in acts if len(a) < 80][:4]


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
    dates = record_dates(record)
    intro_dates = [d for k, d in dates.items() if "FirstReading" in k]
    introduced = min(intro_dates) if intro_dates else None
    latest_move = max(dates.values()) if dates else None
    assent = dates.get("ReceivedRoyalAssentDateTime") or (best_date(record) if passed else None)
    days_to_law = None
    if passed and assent and introduced and assent >= introduced:
        days_to_law = (assent.date() - introduced.date()).days
    now = datetime.now(timezone.utc)
    label = bill_type_label(record, number)
    kind = {PMB_LABEL: "pmb", GOV_LABEL: "gov", SEN_GOV_LABEL: "gov", SEN_PUBLIC_LABEL: "senate"}.get(label, "other")
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
        "dates": dates,
        "stage_term": STAGE_TERMS.get(STAGES[stage_index(status)][0]) if stage_index(status) >= 0 else None,
        "house_origin": is_house_origin(record, number),
        "type_label": label,
        "kind": kind,
        "pro_forma": is_pro_forma(record),
        "introduced": introduced,
        "latest_move": latest_move,
        "assent": assent,
        "days_to_law": days_to_law,
        "is_new": bool(introduced and (now - introduced).days <= 30),
        "moved_recently": bool(latest_move and (now - latest_move).days <= 7),
        "topic": topic_for(f"{long} {short}"),
        "amends": amended_acts(long),
    }


ACTIVE_SORTS = ("progress", "recent", "number")
ACTIVE_KINDS = ("gov", "pmb", "senate")
ACTIVE_CHAMBERS = ("house", "senate")


def all_active_bills(records: list[dict], chamber: str = "", kind: str = "",
                     q: str = "", sort: str = "progress") -> list[dict]:
    """Every bill still moving, filtered and sorted. Pro forma placeholders are left out."""
    bills = [b for b in (normalize(r) for r in records)
             if b and is_active(b["status"]) and not b["pro_forma"]]
    if chamber in ACTIVE_CHAMBERS:
        bills = [b for b in bills if b["chamber_class"] == chamber]
    if kind in ACTIVE_KINDS:
        bills = [b for b in bills if b["kind"] == kind]
    q = q.strip().lower()
    if q:
        bills = [b for b in bills if q in f"{b['number']} {b['title']} {b['short_title']}".lower()]

    epoch = datetime.min.replace(tzinfo=timezone.utc)
    # Stable sorts, least significant key first.
    bills.sort(key=lambda b: bill_sort_key(b["number"]))
    if sort == "number":
        return bills
    if sort == "recent":
        bills.sort(key=lambda b: b["latest_move"] or epoch, reverse=True)
        return bills
    # Default: furthest along its path, then most recent activity. Dated bills
    # outrank undated ones, because the feed leaves dates blank on some records.
    bills.sort(key=lambda b: b["stage_index"], reverse=True)
    bills.sort(key=lambda b: b["active_date"] or epoch, reverse=True)
    return bills


def top_active_bills(records: list[dict], limit: int = TOP_ACTIVE) -> list[dict]:
    return all_active_bills(records)[:limit]


def recent_passed_bills(records: list[dict], limit: int = TOP_PASSED) -> tuple[list[dict], bool]:
    """Newest royal assents first. Returns (bills, order_is_approximate)."""
    bills = [b for b in (normalize(r) for r in records) if b and b["passed"]]
    epoch = datetime.min.replace(tzinfo=timezone.utc)
    bills.sort(key=lambda b: bill_sort_key(b["number"]), reverse=True)  # fallback order
    bills.sort(key=lambda b: b["sort_date"] or epoch, reverse=True)
    top = bills[:limit]
    approximate = any(b["sort_date"] is None for b in top)
    return top, approximate


def time_to_law_summary(bills: list[dict]) -> dict | None:
    """Average, fastest and slowest days from first reading to royal assent."""
    timed = [b for b in bills if b["days_to_law"] is not None]
    if not timed:
        return None
    fastest = min(timed, key=lambda b: b["days_to_law"])
    slowest = max(timed, key=lambda b: b["days_to_law"])
    return {
        "average": round(sum(b["days_to_law"] for b in timed) / len(timed)),
        "fastest": fastest, "slowest": slowest, "count": len(timed),
    }


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


def _first_int(item: dict, keys: tuple[str, ...]) -> int | None:
    for key in keys:
        value = item.get(key)
        if isinstance(value, int) and not isinstance(value, bool):
            return value
    return None


def _votes(raw_list) -> list[dict]:
    out = []
    for item in raw_list if isinstance(raw_list, list) else []:
        if not isinstance(item, dict):
            continue
        yeas = _first_int(item, ("DivisionVotesYeas", "VotesYeas", "Yeas"))
        nays = _first_int(item, ("DivisionVotesNays", "VotesNays", "Nays"))
        if yeas is None or nays is None:
            continue
        out.append({"division": _first_int(item, ("DivisionNumber",)), "yeas": yeas, "nays": nays,
                    "paired": _first_int(item, ("DivisionVotePaired", "VotesPaired", "Paired"))})
    return out


IN_FORCE_RE = re.compile(r"(?:comes?|coming) into (?:force|effect)", re.IGNORECASE)


def find_in_force(summary_html: str) -> str | None:
    """A sentence from the summary that says when the bill takes effect, if it has one."""
    if not summary_html:
        return None
    text = html_lib.unescape(re.sub(r"<[^>]+>", " ", re.sub(r"(?i)<br\s*/?>", ". ", summary_html)))
    text = re.sub(r"\s+", " ", text)
    for sent in SENTENCE_SPLIT.split(text):
        if IN_FORCE_RE.search(sent):
            return trim_text(sent.strip(" ."), 240).rstrip(".") + "."
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
                "house_votes": _votes(raw.get("HouseVoteDetails")),
                "senate_votes": _votes(raw.get("SenateVoteDetails")),
                "in_force": find_in_force(raw.get("ShortLegislativeSummaryEn") or ""),
                "speeches": extract_speeches(raw),
                "committees": extract_committees(raw),
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
_members_fetch_lock = threading.Lock()


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
    directory = get_directory()
    if directory["members"]:
        return {m["id"]: m["party"] for m in directory["members"] if m["party"] and m["party"] != "Unknown"}
    with _members_fetch_lock:
        return _get_member_parties_locked()


def _get_member_parties_locked() -> dict[int, str]:
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
            "topic": topic_for(f"{pick(rec, LONG_TITLE_KEYS)} {pick(rec, SHORT_TITLE_KEYS)}"),
            "number": number,
            "type": bill_type_label(rec, number),
            "group": status_group(status),
            "house": is_house_origin(rec, number),
        })
    return rows


def make_donut(items: list[tuple[str, int, str]]) -> dict | None:
    """Donut data for an SVG ring: each legend entry carries its arc (dash, gap, offset),
    measured on a circle whose circumference is 100 so counts map straight to percent."""
    items = [(label, count, colour) for label, count, colour in items if count > 0]
    total = sum(count for _, count, _ in items)
    if not total:
        return None
    legend, running = [], 0.0
    for idx, (label, count, colour) in enumerate(items):
        length = count / total * 100
        dash = length if len(items) == 1 else max(length - 0.6, 0.05)  # hairline gap between arcs
        pct = count / total * 100
        legend.append({"idx": idx, "label": label, "count": count, "colour": colour,
                       "pct": "<1" if pct < 1 else f"{pct:.0f}",
                       "dash": round(dash, 3), "gap": round(100 - dash, 3), "offset": round(-running, 3)})
        running += length
    return {"total": total, "legend": legend}


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


def monthly_laws(passed_bills: list[dict]) -> list[dict]:
    """Bills that received royal assent, counted by month (empty months included)."""
    counts = Counter((b["assent"].year, b["assent"].month) for b in passed_bills if b["assent"])
    if not counts:
        return []
    top = max(counts.values())
    (y, m), end = min(counts), max(counts)
    out = []
    while (y, m) <= end:
        n = counts.get((y, m), 0)
        out.append({"label": date(y, m, 1).strftime("%b %Y"), "count": n, "width": round(n / top * 100)})
        y, m = (y + 1, 1) if m == 12 else (y, m + 1)
    return out


def topic_bars(rows: list[dict]) -> list[dict]:
    counts = Counter(r["topic"] for r in rows)
    order = sorted((t for t in counts if t != "Other"), key=lambda t: -counts[t])
    if "Other" in counts:
        order.append("Other")
    top = max(counts.values(), default=1)
    return [{"label": t, "count": counts[t], "width": round(counts[t] / top * 100)} for t in order]


def origin_stats(records: list[dict]) -> dict | None:
    """Where bills start, and how many have crossed to the other chamber."""
    house_n = senate_n = house_reached_senate = senate_reached_house = 0
    house_third = senate_third = 0
    for rec in records:
        number = pick(rec, NUMBER_KEYS)
        if not number or is_pro_forma(rec):
            continue
        dates = record_dates(rec)
        if any("PassedHouseThirdReading" in k for k in dates):
            house_third += 1
        if any("PassedSenateThirdReading" in k for k in dates):
            senate_third += 1
        if is_house_origin(rec, number):
            house_n += 1
            house_reached_senate += any("PassedSenateFirstReading" in k for k in dates)
        else:
            senate_n += 1
            senate_reached_house += any("PassedHouseFirstReading" in k for k in dates)
    if not (house_n or senate_n):
        return None
    return {
        "donut": make_donut([("Started in the House of Commons", house_n, "#2b2d31"),
                             ("Started in the Senate", senate_n, "#a9acb3")]),
        "house_n": house_n, "senate_n": senate_n,
        "house_reached_senate": house_reached_senate, "senate_reached_house": senate_reached_house,
        "house_third": house_third, "senate_third": senate_third,
    }


def recent_introductions(records: list[dict], days: int = 30, limit: int = 8) -> dict:
    bills = [b for b in (normalize(r) for r in records) if b and not b["pro_forma"] and b["is_new"]
             and (datetime.now(timezone.utc) - b["introduced"]).days <= days]
    bills.sort(key=lambda b: b["introduced"], reverse=True)
    return {"days": days, "count": len(bills), "bills": bills[:limit]}


def top_sponsors(party_rows: list[dict], limit: int = 8) -> list[dict]:
    counts = Counter((r["sponsor"], r["party"]) for r in party_rows if r.get("sponsor"))
    return [{"name": n, "party": p, "count": c, "colour": PARTY_COLOURS.get(p, OTHER_COLOUR)}
            for (n, p), c in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0][0]))[:limit]]


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
            return {"number": number, "type": type_label, "party": party or "Unknown", "ok": info is not None,
                    "sponsor": (info or {}).get("sponsor_name") or ""}

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


# --------------------------------------------------------------------------
# Glossary: plain-language definitions shown in the pop-ups and on /glossary
# --------------------------------------------------------------------------
GLOSSARY = (
    ("First reading", "The formal introduction of a bill. There is no debate on its content. The bill is simply put before the chamber and printed."),
    ("Second reading", "Members debate the bill's main idea (its principle) and vote on whether it should go further. If it passes, the bill goes to committee."),
    ("Committee stage", "A smaller group of MPs or senators studies the bill in detail, often hears from experts and the public, and can propose changes clause by clause."),
    ("Report stage", "After committee, the whole chamber looks at any changes the committee made, and members can propose more amendments."),
    ("Third reading", "The final debate and vote on the bill, as amended, in a chamber. If it passes, the bill moves to the other chamber or to royal assent."),
    ("Royal assent", "The final step. The Governor General, or a deputy, signs a bill that has passed both chambers, and it becomes law. It may take effect right away or on a later date set in the bill."),
    ("Coming into force", "The date a law actually takes effect. It can be the day of royal assent, a fixed date, or a date the government sets later by order."),
    ("Government bill", "A bill introduced by a cabinet minister, usually to carry out the government's policy. Government bills get priority in House time."),
    ("Private member's bill", "A bill introduced by an MP who isn't a cabinet minister. Few become law, because government bills take most of the House's time."),
    ("Order of Precedence", "The ranked list of private members' bills eligible for debate in the House. Bills get a place by random draw. Bills outside the Order of Precedence are still waiting for a spot."),
    ("Senate public bill", "A bill introduced in the Senate by a senator who isn't representing the government."),
    ("Pro forma bill", "A placeholder bill (such as C-1 and S-1) introduced at the start of a session to assert Parliament's right to run its own business before it deals with the Speech from the Throne. It is never debated."),
    ("Omnibus bill", "A very large bill that changes many laws at once, often on different subjects."),
    ("Sponsor", "The MP or senator who introduces a bill and speaks for it."),
    ("Recorded vote (division)", "A vote where each member's yes or no is counted and published. Paired members agree not to vote so that their absences cancel each other out."),
    ("Confidence vote", "A vote the government must win to stay in power. Losing one can lead to an election."),
    ("Prorogation", "The end of a session of Parliament without an election. Bills that haven't passed generally die and must be reintroduced."),
    ("Dissolution", "The formal end of a Parliament, which triggers a federal election."),
    ("Died on the Order Paper", "A bill that never finished before the session ended, so it stopped moving."),
)


def _slug(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")


GLOSSARY_BY_SLUG = {_slug(term): {"term": term, "text": text} for term, text in GLOSSARY}
STAGE_TERMS = {"First reading": "first-reading", "Second reading": "second-reading",
               "Committee": "committee-stage", "Report stage": "report-stage",
               "Third reading": "third-reading", "Royal assent": "royal-assent"}


def _static_version(filename: str) -> int:
    """Changes whenever a static file is rebuilt, so browsers fetch the new copy."""
    try:
        return int(os.path.getmtime(os.path.join(app.static_folder, filename)))
    except OSError:
        return 0


@app.context_processor
def inject_site_globals():
    return {"glossary_data": GLOSSARY_BY_SLUG, "css_version": _static_version("app.css"),
            "js_version": _static_version("app.js")}


# --------------------------------------------------------------------------
# Speed: browser caching for static files, and gzip for text responses
# --------------------------------------------------------------------------
COMPRESSIBLE = ("text/html", "text/css", "text/csv", "application/json", "image/svg+xml", "application/javascript")


@app.after_request
def speed_up(response: Response) -> Response:
    # The stylesheet's URL carries a version number, so it can be kept for a year.
    if request.endpoint == "static":
        if request.path.endswith(("/app.css", "/app.js")) and request.args.get("v"):
            response.headers["Cache-Control"] = "public, max-age=31536000, immutable"
        else:
            response.headers["Cache-Control"] = "public, max-age=86400"

    accepts_gzip = "gzip" in request.headers.get("Accept-Encoding", "").lower()
    if (not accepts_gzip or response.status_code != 200 or "Content-Encoding" in response.headers
            or response.mimetype not in COMPRESSIBLE):
        return response
    response.direct_passthrough = False  # lets static files be read and compressed too
    data = response.get_data()
    if len(data) < 600:
        return response
    packed = gzip.compress(data, compresslevel=6)
    response.set_data(packed)
    response.headers["Content-Encoding"] = "gzip"
    response.headers["Content-Length"] = str(len(packed))
    response.headers.add("Vary", "Accept-Encoding")
    return response


# --------------------------------------------------------------------------
# Member directory
#
# Two free sources, joined on the member's PersonId:
#   * the House of Commons' own member list (XML): name, riding, province, current party
#   * Open North's Represent API: photo, email, office phone numbers and addresses, website
# If one is down, the directory still builds from the other with fewer details.
# --------------------------------------------------------------------------
XML_MEMBERS_URL = "https://www.ourcommons.ca/members/en/search/xml"
REPRESENT_MPS_URL = "https://represent.opennorth.ca/representatives/house-of-commons/?limit=1000"
POSTCODE_URL = "https://represent.opennorth.ca/postcodes/{code}/"
DIRECTORY_TTL = 12 * 3600
DIRECTORY_FAIL_TTL = 5 * 60
POSTAL_RE = re.compile(r"^[A-Za-z]\d[A-Za-z]\s?\d[A-Za-z]\d$")
PARTY_ORDER = ("Liberal", "Conservative", "Bloc Québécois", "NDP", "Green Party", "Independent")

_directory_cache: dict = {"expires": 0.0, "members": [], "error": None, "contacts": False}
_directory_lock = threading.Lock()
_postal_cache: dict = {}


def _strip_accents(text: str) -> str:
    return "".join(c for c in unicodedata.normalize("NFKD", text) if not unicodedata.combining(c))


def norm_riding(name: str) -> str:
    """Riding names compared loosely: dash styles, accents, spacing and case don't matter."""
    name = re.sub(r"[‐-―−]", "-", name or "")
    return re.sub(r"[^a-z0-9]+", "", _strip_accents(name).lower())


def parse_members_xml(text: str) -> dict[int, dict]:
    """{PersonId: {...}} for every current member in the House's XML list."""
    if not text or len(text) > 8_000_000:
        return {}
    try:
        root = ET.fromstring(text)
    except ET.ParseError:
        return {}
    now = datetime.now(timezone.utc)
    out: dict[int, dict] = {}
    for el in root.iter():
        fields = {child.tag.split("}")[-1]: (child.text or "").strip() for child in el if len(child) == 0}
        if "PersonId" not in fields or "ConstituencyName" not in fields or not fields["PersonId"].isdigit():
            continue
        ended = parse_date(fields.get("ToDateTime", ""))
        if ended and ended < now:
            continue  # a former member
        raw_party = fields.get("CaucusShortName", "")
        out[int(fields["PersonId"])] = {
            "first": fields.get("PersonOfficialFirstName", ""),
            "last": fields.get("PersonOfficialLastName", ""),
            "riding": fields["ConstituencyName"],
            "province": fields.get("ConstituencyProvinceTerritoryName", ""),
            "party": canon_party(raw_party) or raw_party or "Unknown",
        }
    return out


def _clean_tel(tel: str) -> str:
    return re.sub(r"\s+", " ", tel or "").strip()


def parse_represent(payload) -> dict[int, dict]:
    """{PersonId: {...}} from Represent's list of House of Commons MPs."""
    objs = payload.get("objects") if isinstance(payload, dict) else None
    out: dict[int, dict] = {}
    for obj in objs or []:
        if not isinstance(obj, dict):
            continue
        match = re.search(r"\((\d+)\)", obj.get("url") or "")
        if not match:
            continue
        hill_tel, const_tel, const_addr = "", "", []
        for office in obj.get("offices") or []:
            if not isinstance(office, dict):
                continue
            kind = (office.get("type") or "").lower()
            tel = _clean_tel(office.get("tel") or "")
            postal = re.sub(r"\s*\n\s*", ", ", (office.get("postal") or "").strip())
            if "constituency" in kind:
                const_tel = const_tel or tel
                if postal and len(const_addr) < 2:
                    const_addr.append(postal)
            else:
                hill_tel = hill_tel or tel
        photo = obj.get("photo_url") or ""
        out[int(match.group(1))] = {
            "name": (obj.get("name") or "").strip(),
            "party": canon_party(obj.get("party_name") or "") or (obj.get("party_name") or ""),
            "riding": (obj.get("district_name") or "").strip(),
            "email": (obj.get("email") or "").strip(),
            "photo": photo if photo.startswith("https://") else "",
            "website": (obj.get("personal_url") or "").strip(),
            "profile": obj.get("url") or "",
            "hill_tel": hill_tel, "const_tel": const_tel, "const_addr": const_addr,
        }
    return out


def _initials(name: str) -> str:
    parts = [p for p in re.split(r"[\s-]+", name) if p and p[0].isalpha()]
    return (parts[0][0] + parts[-1][0]).upper() if len(parts) > 1 else name[:2].upper()


def _name_sort_key(member: dict) -> str:
    return _strip_accents(member["last"] or member["name"].split(" ")[-1]).lower() + _strip_accents(member["first"]).lower()


def merge_directory(xml: dict[int, dict], rep: dict[int, dict]) -> list[dict]:
    members = []
    for pid in (xml.keys() if xml else rep.keys()):
        x, r = xml.get(pid, {}), rep.get(pid, {})
        name = r.get("name") or f"{x.get('first', '')} {x.get('last', '')}".strip()
        last = x.get("last") or name.split(" ")[-1]
        first = x.get("first") or name[: max(len(name) - len(last), 0)].strip()
        party = x.get("party") or r.get("party") or "Unknown"
        members.append({
            "id": pid, "name": name, "first": first, "last": last,
            "party": party, "riding": x.get("riding") or r.get("riding", ""),
            "province": x.get("province", ""),
            "email": r.get("email", ""), "photo": r.get("photo", ""),
            "website": r.get("website", ""), "profile": r.get("profile", ""),
            "hill_tel": r.get("hill_tel", ""), "const_tel": r.get("const_tel", ""),
            "const_addr": r.get("const_addr", []),
            "initials": _initials(name),
            "search": _strip_accents(f"{name} {x.get('riding') or r.get('riding', '')} {x.get('province', '')} {party}").lower(),
        })
    members = [m for m in members if m["name"]]
    members.sort(key=_name_sort_key)
    return members


def get_directory(force: bool = False) -> dict:
    """{'members': [...], 'error': str|None, 'contacts': bool}, cached for 12 hours."""
    now = time.time()
    with _directory_lock:
        if not force and now < _directory_cache["expires"]:
            return _directory_cache
        xml, rep, problems = {}, {}, []
        try:
            resp = requests.get(XML_MEMBERS_URL, timeout=25, headers={"User-Agent": "legis-bill-tracker/1.0"})
            resp.raise_for_status()
            xml = parse_members_xml(resp.content.decode("utf-8-sig", errors="replace"))
        except requests.RequestException as exc:
            problems.append(f"member list ({exc})")
        try:
            resp = requests.get(REPRESENT_MPS_URL, timeout=30,
                                headers={"Accept": "application/json", "User-Agent": "legis-bill-tracker/1.0"})
            resp.raise_for_status()
            rep = parse_represent(json.loads(resp.content.decode("utf-8-sig")))
        except (requests.RequestException, ValueError) as exc:
            problems.append(f"contact details ({exc})")
        members = merge_directory(xml, rep)
        _directory_cache.update(
            members=members,
            contacts=bool(rep),
            error=None if members else "Could not load the member list: " + "; ".join(problems),
            expires=now + (DIRECTORY_TTL if members else DIRECTORY_FAIL_TTL),
        )
        return _directory_cache


def party_groups(members: list[dict]) -> list[dict]:
    """Members grouped by party: the biggest caucuses first, independents and others last."""
    by_party: dict[str, list[dict]] = {}
    for m in members:
        by_party.setdefault(m["party"], []).append(m)

    def order(party: str):
        if party in PARTY_ORDER and party != "Independent":
            return (0, -len(by_party[party]), party)
        return (1, 0 if party == "Independent" else 1, party)

    return [{"party": p, "slug": _slug(p), "colour": PARTY_COLOURS.get(p, OTHER_COLOUR), "members": by_party[p]}
            for p in sorted(by_party, key=order)]


def lookup_riding(postal: str) -> tuple[list[str], str | None]:
    """Riding name(s) for a postal code via Represent. Returns (names, error message)."""
    code = re.sub(r"\s+", "", postal).upper()
    if not POSTAL_RE.match(code):
        return [], "That doesn't look like a Canadian postal code. Try something like K1A 0A9."
    now = time.time()
    hit = _postal_cache.get(code)
    if hit and now < hit[0]:
        return hit[1], None
    try:
        resp = requests.get(POSTCODE_URL.format(code=code), timeout=12,
                            headers={"Accept": "application/json", "User-Agent": "legis-bill-tracker/1.0"})
        if resp.status_code == 404:
            return [], "No riding was found for that postal code."
        resp.raise_for_status()
        data = resp.json()
    except (requests.RequestException, ValueError):
        return [], "The postal-code lookup is unavailable right now. Try again in a minute, or browse the list below."
    names = []
    for key in ("boundaries_centroid", "boundaries_concordance"):
        for item in data.get(key) or []:
            if isinstance(item, dict) and item.get("name") and item["name"] not in names:
                names.append(item["name"])
    if len(_postal_cache) > 500:
        _postal_cache.clear()
    _postal_cache[code] = (now + DIRECTORY_TTL, names)
    return names, None if names else "No riding was found for that postal code."


def find_my_mps(postal: str, members: list[dict]) -> dict:
    names, error = lookup_riding(postal)
    wanted = {norm_riding(n) for n in names}
    matches = [m for m in members if norm_riding(m["riding"]) in wanted]
    if not error and not matches:
        error = ("Your riding is " + " / ".join(names) + ", but no sitting MP matched that name. "
                 "Riding names changed recently, so search the list below by name or riding.")
    return {"postal": re.sub(r"\s+", "", postal).upper(), "ridings": names, "matches": matches, "error": error}


# --------------------------------------------------------------------------
# Bill timeline (dates come from the list feed)
# --------------------------------------------------------------------------
def build_timeline(bill: dict) -> list[dict]:
    dates = bill["dates"]
    chambers = (("House", "House of Commons"), ("Senate", "Senate"))
    if not bill["house_origin"]:
        chambers = chambers[::-1]

    steps: list[dict] = []
    for key, where in chambers:
        third = dates.get(f"Passed{key}ThirdReadingDateTime")
        steps += [
            {"label": "First reading", "where": where, "term": "first-reading",
             "date": dates.get(f"Passed{key}FirstReadingDateTime"), "done": bool(dates.get(f"Passed{key}FirstReadingDateTime"))},
            {"label": "Second reading", "where": where, "term": "second-reading",
             "date": dates.get(f"Passed{key}SecondReadingDateTime"), "done": bool(dates.get(f"Passed{key}SecondReadingDateTime"))},
            {"label": "Committee study", "where": where, "term": "committee-stage", "date": None, "done": bool(third)},
            {"label": "Third reading", "where": where, "term": "third-reading", "date": third, "done": bool(third)},
        ]
    steps.append({"label": "Royal assent", "where": "Governor General", "term": "royal-assent",
                  "date": bill["assent"], "done": bool(bill["passed"] or bill["assent"])})

    still_moving = is_active(bill["status"]) and not bill["pro_forma"]
    current_marked = False
    for step in steps:
        if step["done"]:
            step["state"] = "done"
        elif still_moving and not current_marked:
            step["state"], current_marked = "current", True
        else:
            step["state"] = "upcoming"
    return steps


# --------------------------------------------------------------------------
# CSV export
# --------------------------------------------------------------------------
def _safe_cell(value) -> str:
    text = "" if value is None else str(value)
    return "'" + text if text[:1] in ("=", "+", "-", "@", "\t", "\r") else text


def csv_response(filename: str, header: list[str], rows: list[list]) -> Response:
    buf = io.StringIO()
    writer = csv.writer(buf)
    writer.writerow(header)
    for row in rows:
        writer.writerow([_safe_cell(c) for c in row])
    response = Response("﻿" + buf.getvalue(), mimetype="text/csv")  # BOM so Excel reads accents
    response.headers["Content-Disposition"] = f'attachment; filename="{filename}"'
    return response


def bills_csv(bills: list[dict], filename: str) -> Response:
    header = ["Bill", "Short title", "Title", "Status", "Type", "Started in", "Currently in", "Topic",
              "Introduced", "Royal assent", "Days to law", "Amends"]
    rows = [[b["number"], b["short_title"], b["title"], b["status"], b["type_label"], b["chamber"],
             b["current_chamber"], b["topic"],
             b["introduced"].date().isoformat() if b["introduced"] else "",
             b["assent"].date().isoformat() if b["assent"] else "",
             b["days_to_law"] if b["days_to_law"] is not None else "",
             "; ".join(b["amends"])] for b in bills]
    return csv_response(filename, header, rows)


# --------------------------------------------------------------------------
# Debates and committee studies, read from each bill's own JSON
# --------------------------------------------------------------------------
HANSARD_SITTING_URL = "https://www.ourcommons.ca/DocumentViewer/en/{session}/house/sitting-{sitting}/hansard"
OPENPARLIAMENT_BILL_URL = "https://openparliament.ca/bills/{session}/{number}/"
TRUSTED_LINK_HOSTS = ("sencanada.ca", "www.sencanada.ca", "www.ourcommons.ca")
COMMITTEE_ACRONYM_RE = re.compile(r"^[A-Z]{2,8}$")
HOUSE_COMMITTEE_URL = "https://www.ourcommons.ca/Committees/en/{acr}"
HOUSE_COMMITTEE_MEMBERS_URL = "https://www.ourcommons.ca/Committees/en/{acr}/Members"
COMMITTEE_LIST_URL = "https://www.ourcommons.ca/Committees/en/List"


def _walk(node):
    """Every dict inside a nested JSON structure."""
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, dict):
            yield cur
            stack.extend(v for v in cur.values() if isinstance(v, (dict, list)))
        elif isinstance(cur, list):
            stack.extend(v for v in cur if isinstance(v, (dict, list)))


def _safe_url(url) -> str:
    """Only pass along links to Parliament's own sites."""
    if not isinstance(url, str) or not url.startswith("https://"):
        return ""
    host = url[len("https://"):].split("/", 1)[0].lower()
    return url if host in TRUSTED_LINK_HOSTS else ""


def extract_speeches(raw: dict) -> list[dict]:
    """Sponsor's speeches and other recorded interventions, oldest first."""
    seen, out = set(), []
    for item in _walk(raw):
        if not ("EventTypeName" in item and "PersonName" in item and "SpeechDateTime" in item):
            continue
        key = (item.get("InterventionEventId") or item.get("PersonId"), item.get("SpeechDateTime"), item.get("EventTypeId"))
        if key in seen:
            continue
        seen.add(key)
        when = parse_date(str(item.get("SpeechDateTime") or ""))
        out.append({
            "name": str(item.get("PersonName") or "").strip(),
            "party": str(item.get("CaucusShortNameEn") or item.get("CaucusShortName") or "").strip(),
            "kind": str(item.get("EventTypeNameEn") or item.get("EventTypeName") or "").strip(),
            "date": when.date().isoformat() if when else "",
            "senate": item.get("ChamberOrganizationId") == 2,
            "sitting": str(item.get("MeetingNumber") or "").strip(),
            "url": _safe_url(item.get("UrlEn") or item.get("Url") or ""),
        })
    out = [s for s in out if s["name"]]
    out.sort(key=lambda s: s["date"])
    return out[-40:]


def extract_committees(raw: dict) -> list[dict]:
    """Committees that have studied the bill, with how many meetings they held on it."""
    by_acr: dict[str, dict] = {}
    for item in _walk(raw):
        acr = item.get("CommitteeAcronym")
        if not isinstance(acr, str) or not COMMITTEE_ACRONYM_RE.match(acr.strip().upper()):
            continue
        acr = acr.strip().upper()
        entry = by_acr.setdefault(acr, {"acr": acr, "name": "", "meetings": set(), "dates": set()})
        name = item.get("CommitteeNameEn") or item.get("CommitteeName")
        if name and not entry["name"]:
            entry["name"] = str(name).strip()
        if "Number" in item and item.get("Date"):
            when = parse_date(str(item["Date"]))
            if when:
                entry["meetings"].add((str(item["Number"]), when.date().isoformat()))
                entry["dates"].add(when.date().isoformat())
    out = []
    for entry in by_acr.values():
        dates = sorted(entry["dates"])
        out.append({"acr": entry["acr"], "name": entry["name"] or entry["acr"], "meetings": len(entry["meetings"]),
                    "first": dates[0] if dates else "", "last": dates[-1] if dates else "",
                    "senate": "senate" in entry["name"].lower()})
    out.sort(key=lambda c: c["first"] or "9999")
    return out


def speech_link(speech: dict, parl_session: str) -> str:
    """A link to the debate: the Senate gives one per speech, the House gives a sitting number."""
    if speech["url"]:
        return speech["url"]
    if not speech["senate"] and speech["sitting"].isdigit():
        return HANSARD_SITTING_URL.format(session=parl_session, sitting=speech["sitting"])
    return ""


# --------------------------------------------------------------------------
# Committees: list, and each committee's members (read from the House of Commons site)
# --------------------------------------------------------------------------
COMMITTEE_NAMES = {
    "ACVA": "Veterans Affairs", "AGRI": "Agriculture and Agri-Food", "CHPC": "Canadian Heritage",
    "CIMM": "Citizenship and Immigration", "ENVI": "Environment and Sustainable Development",
    "ETHI": "Access to Information, Privacy and Ethics", "FAAE": "Foreign Affairs and International Development",
    "FEWO": "Status of Women", "FINA": "Finance", "FOPO": "Fisheries and Oceans", "HESA": "Health",
    "HUMA": "Human Resources, Skills and Social Development and the Status of Persons with Disabilities",
    "INAN": "Indigenous and Northern Affairs", "INDU": "Industry and Technology",
    "JUST": "Justice and Human Rights", "LANG": "Official Languages", "NDDN": "National Defence",
    "OGGO": "Government Operations and Estimates", "PACP": "Public Accounts", "PROC": "Procedure and House Affairs",
    "RNNR": "Natural Resources", "SECU": "Public Safety and National Security",
    "TRAN": "Transport, Infrastructure and Communities", "CIIT": "International Trade", "LIAI": "Liaison",
}
COMMITTEE_LINK_RE = re.compile(r"/Committees/en/([A-Z]{3,6})(?=[\"'?#/]|$)")
COMMITTEE_TTL = 12 * 3600
COMMITTEE_FAIL_TTL = 5 * 60

_committee_list_cache: dict = {"expires": 0.0, "items": []}
_committee_cache: dict = {}
_committee_lock = threading.Lock()


def parse_committee_list(page_html: str) -> list[str]:
    acronyms: list[str] = []
    for match in COMMITTEE_LINK_RE.finditer(page_html):
        if match.group(1) not in acronyms:
            acronyms.append(match.group(1))
    return acronyms


def get_committee_list() -> list[dict]:
    now = time.time()
    with _committee_lock:
        if now < _committee_list_cache["expires"]:
            return _committee_list_cache["items"]
    acronyms: list[str] = []
    try:
        resp = requests.get(COMMITTEE_LIST_URL, timeout=20, headers={"User-Agent": "legis-bill-tracker/1.0"})
        resp.raise_for_status()
        acronyms = parse_committee_list(resp.text)
    except requests.RequestException:
        acronyms = []
    if len(acronyms) < 5:  # a real list has dozens; fewer means the page changed
        acronyms = list(COMMITTEE_NAMES)
    items = [{"acr": a, "name": COMMITTEE_NAMES.get(a, "")} for a in acronyms]
    with _committee_lock:
        _committee_list_cache.update(items=items, expires=now + COMMITTEE_TTL)
    return items


def parse_committee_page(page_html: str) -> dict:
    """{'name': str, 'people': [(PersonId, role)]} from a committee's Members page.

    The page groups members under headings (Chair, Vice-Chairs, Members, Associate Members),
    so a member's role is the last heading seen before their link."""
    title = re.search(r"<h1[^>]*>(.*?)</h1>", page_html, re.IGNORECASE | re.DOTALL)
    name = html_to_text(title.group(1)) if title else ""
    people: list[tuple[int, str]] = []
    seen: set[int] = set()
    role = "Member"
    last_end = 0
    for match in MEMBER_LINK_RE.finditer(page_html):
        tail = html_to_text(page_html[last_end:match.start()])[-60:].lower()
        if "associate" in tail:
            role = "Associate"
        elif re.search(r"vice-?\s?chairs?\W*$", tail):
            role = "Vice-Chair"
        elif re.search(r"\bchair\W*$", tail):
            role = "Chair"
        elif re.search(r"\bmembers?\W*$", tail):
            role = "Member"
        last_end = match.end()
        pid = int(match.group(1))
        if pid not in seen and role != "Associate":
            seen.add(pid)
            people.append((pid, role))
    return {"name": name, "people": people}


def get_committee(acr: str) -> dict | None:
    key = acr.upper()
    now = time.time()
    with _committee_lock:
        hit = _committee_cache.get(key)
    if hit and now < hit["expires"]:
        return hit["data"]
    data = None
    try:
        resp = requests.get(HOUSE_COMMITTEE_MEMBERS_URL.format(acr=key), timeout=20,
                            headers={"User-Agent": "legis-bill-tracker/1.0"})
        if resp.status_code == 200:
            parsed = parse_committee_page(resp.text)
            if parsed["people"]:
                data = parsed
    except requests.RequestException:
        data = None
    with _committee_lock:
        _committee_cache[key] = {"data": data, "expires": now + (COMMITTEE_TTL if data else COMMITTEE_FAIL_TTL)}
    return data


# --------------------------------------------------------------------------
# Senators (unofficial: read from Wikipedia's list, because the Senate's own list isn't machine readable)
# --------------------------------------------------------------------------
SENATE_LIST_URL = "https://en.wikipedia.org/wiki/List_of_current_senators_of_Canada"
SENATE_OFFICIAL_URL = "https://sencanada.ca/en/senators/"
SENATE_TTL = 12 * 3600
SENATE_GROUPS = {
    "ISG": "Independent Senators Group", "CSG": "Canadian Senators Group", "PSG": "Progressive Senate Group",
    "CPC": "Conservative", "C": "Conservative", "NA": "Non-affiliated", "N/A": "Non-affiliated",
}
SENATE_GROUP_COLOURS = {
    "Independent Senators Group": "#4a6fa5", "Canadian Senators Group": "#8a6d3b", "Progressive Senate Group": "#3d9b35",
    "Conservative": "#1a4782", "Non-affiliated": "#8a8d93",
}
PROVINCES = {
    "NL": "Newfoundland and Labrador", "PE": "Prince Edward Island", "PEI": "Prince Edward Island", "NS": "Nova Scotia",
    "NB": "New Brunswick", "QC": "Quebec", "QUE": "Quebec", "ON": "Ontario", "ONT": "Ontario", "MB": "Manitoba",
    "SK": "Saskatchewan", "AB": "Alberta", "BC": "British Columbia", "YT": "Yukon", "NT": "Northwest Territories",
    "NU": "Nunavut",
}

_senate_cache: dict = {"expires": 0.0, "senators": [], "error": None}
_senate_lock = threading.Lock()


class _TableParser(HTMLParser):
    """Collects every table as rows of cells: {'text', 'href'}."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.tables: list[list[list[dict]]] = []
        self._row: list[dict] | None = None
        self._cell: dict | None = None
        self._skip = 0

    def handle_starttag(self, tag, attrs):
        if tag == "table":
            self.tables.append([])
        elif tag == "tr" and self.tables:
            self._row = []
            self.tables[-1].append(self._row)
        elif tag in ("td", "th") and self._row is not None:
            self._cell = {"text": "", "href": ""}
            self._row.append(self._cell)
        elif tag in ("sup", "style", "script") and self._cell is not None:
            self._skip += 1
        elif tag == "a" and self._cell is not None and not self._cell["href"]:
            href = dict(attrs).get("href") or ""
            if href.startswith("/wiki/") and ":" not in href:
                self._cell["href"] = "https://en.wikipedia.org" + href

    def handle_endtag(self, tag):
        if tag in ("td", "th"):
            self._cell = None
        elif tag in ("sup", "style", "script") and self._skip:
            self._skip -= 1

    def handle_data(self, data):
        if self._cell is not None and not self._skip:
            self._cell["text"] += data


def parse_senators(page_html: str) -> list[dict]:
    parser = _TableParser()
    try:
        parser.feed(page_html)
        parser.close()
    except Exception:
        pass
    for table in parser.tables:
        header = next((row for row in table if row and any("name" in c["text"].lower() for c in row)), None)
        if not header:
            continue
        labels = [re.sub(r"\s+", " ", c["text"]).strip().lower() for c in header]

        def col(*words):
            return next((i for i, label in enumerate(labels) if any(w in label for w in words)), None)

        name_i, group_i = col("name"), col("affiliation", "group", "party")
        prov_i, retire_i = col("province", "division"), col("retirement")
        if name_i is None or group_i is None or prov_i is None:
            continue
        senators = []
        for row in table[table.index(header) + 1:]:
            if len(row) <= max(name_i, group_i, prov_i):
                continue
            clean = lambda i: re.sub(r"\s+", " ", re.sub(r"\[[^\]]*\]", "", row[i]["text"])).strip() if i is not None and i < len(row) else ""
            name = clean(name_i)
            if not name or name.lower() in ("vacant", "name"):
                continue
            abbr = clean(group_i)
            prov = clean(prov_i)
            senators.append({
                "name": name,
                "group": SENATE_GROUPS.get(abbr.upper(), abbr or "Unknown"),
                "province": PROVINCES.get(prov.upper(), prov),
                "retires": clean(retire_i),
                "wiki": row[name_i]["href"],
                "initials": _initials(name),
            })
        if len(senators) >= 50:  # a real list has about a hundred
            return senators
    return []


def get_senators() -> dict:
    now = time.time()
    with _senate_lock:
        if now < _senate_cache["expires"]:
            return _senate_cache
        senators, error = [], None
        try:
            resp = requests.get(SENATE_LIST_URL, timeout=25,
                                headers={"User-Agent": "ParlTrackCanada/1.0 (https://parltrack-canada.onrender.com)"})
            resp.raise_for_status()
            senators = parse_senators(resp.text)
        except requests.RequestException as exc:
            error = str(exc)
        if not senators:
            error = error or "the list's layout was not recognised"
        for s in senators:
            s["search"] = _strip_accents(f"{s['name']} {s['province']} {s['group']}").lower()
        senators.sort(key=lambda s: _strip_accents(s["name"].split(" ")[-1]).lower())
        _senate_cache.update(senators=senators, error=None if senators else f"Could not load the Senate list: {error}",
                             expires=now + (SENATE_TTL if senators else DIRECTORY_FAIL_TTL))
        return _senate_cache


def senate_groups(senators: list[dict]) -> list[dict]:
    by_group: dict[str, list[dict]] = {}
    for s in senators:
        by_group.setdefault(s["group"], []).append(s)
    order = sorted(by_group, key=lambda g: (g == "Non-affiliated", -len(by_group[g]), g))
    return [{"party": g, "slug": _slug(g), "colour": SENATE_GROUP_COLOURS.get(g, OTHER_COLOUR), "members": by_group[g]}
            for g in order]


def warm_up() -> None:
    """Load the slow data in the background right after the server starts."""
    try:
        fetch_records()
        get_directory()
    except Exception:
        pass


def _int_arg(name: str, default: int, low: int, high: int) -> int:
    try:
        value = int(request.args.get(name, default))
    except (TypeError, ValueError):
        return default
    return max(low, min(high, value))


def _active_filters() -> tuple[str, str, str, str]:
    chamber = request.args.get("chamber", "")
    kind = request.args.get("kind", "")
    sort = request.args.get("sort", "progress")
    q = request.args.get("q", "").strip()[:80]
    return (chamber if chamber in ACTIVE_CHAMBERS else "",
            kind if kind in ACTIVE_KINDS else "",
            sort if sort in ACTIVE_SORTS else "progress",
            q)


@app.route("/")
def index():
    records, warning = fetch_records()
    chamber, kind, sort, q = _active_filters()
    limit = _int_arg("limit", TOP_ACTIVE, TOP_ACTIVE, 400)

    matches = all_active_bills(records, chamber, kind, q, sort)
    bills = matches[:limit]
    filters = {k: v for k, v in (("chamber", chamber), ("kind", kind), ("q", q),
                                 ("sort", sort if sort != "progress" else "")) if v}
    more_url = url_for("index", limit=limit + TOP_ACTIVE, **filters) if len(matches) > limit else None
    if records and not matches and not warning and not (chamber or kind or q):
        warning = ("The feed loaded, but no bills could be read from it. LEGISinfo may have "
                   "renamed its fields; open /debug to see the keys it returns.")
    return render_template(
        "index.html",
        active_tab="active",
        bills=bills,
        match_count=len(matches),
        more_url=more_url,
        chamber=chamber, kind=kind, sort=sort, q=q,
        filtered=bool(chamber or kind or q),
        export_url=url_for("export_active", **{k: v for k, v in (("chamber", chamber), ("kind", kind), ("q", q), ("sort", sort)) if v}),
        stages=[label for label, _ in STAGES],
        warning=warning,
        total=len(records),
        fetched_at=_fetched_at(),
    )


@app.route("/passed")
def passed():
    records, warning = fetch_records()
    limit = _int_arg("limit", TOP_PASSED, TOP_PASSED, 400)
    everything, approximate = recent_passed_bills(records, limit=10**6)
    bills = everything[:limit]
    return render_template(
        "passed.html",
        active_tab="passed",
        bills=bills,
        total_passed=len(everything),
        more_url=url_for("passed", limit=limit + TOP_PASSED) if len(everything) > limit else None,
        law_speed=time_to_law_summary(everything),
        export_url=url_for("export_passed"),
        approximate=any(b["sort_date"] is None for b in bills),
        stages=[label for label, _ in STAGES],
        warning=warning,
        total=len(records),
        fetched_at=_fetched_at(),
    )


@app.route("/following")
def following():
    """Cards for the bills a visitor has starred. The list lives in their browser and
    arrives as ?b=C-2,S-3, so the server never stores anything about visitors."""
    wanted = []
    for part in request.args.get("b", "").split(",")[:60]:
        part = part.strip().upper()
        if BILL_NUMBER_RE.match(part) and part not in wanted:
            wanted.append(part)
    records, warning = fetch_records()
    by_number = {}
    for rec in records:
        bill = normalize(rec)
        if bill and bill["number"].upper() in wanted:
            by_number[bill["number"].upper()] = bill
    bills = [by_number[n] for n in wanted if n in by_number]
    return render_template(
        "following.html",
        active_tab=None,
        bills=bills,
        export_url=url_for("export_following", b=",".join(wanted)) if bills else None,
        asked=len(wanted),
        stages=[label for label, _ in STAGES],
        warning=warning,
        total=len(records),
        fetched_at=_fetched_at(),
    )


@app.route("/api/bill/<parl_session>/<number>")
def bill_meta_api(parl_session: str, number: str):
    """Sponsor, party and recorded votes for one bill; loaded into cards after the page appears."""
    if not SESSION_RE.match(parl_session) or not BILL_NUMBER_RE.match(number):
        abort(404)
    info = fetch_bill_json(parl_session, number.upper())
    if not info:
        response = jsonify(ok=False)
        response.headers["Cache-Control"] = "public, max-age=60"
        return response
    party = None
    if info["sponsor_id"]:
        party = get_member_parties().get(info["sponsor_id"]) or canon_party(info["sponsor_caucus"] or "")
    response = jsonify(
        ok=True,
        sponsor=info["sponsor_name"], sponsor_title=info["sponsor_title"],
        riding=info["sponsor_riding"], party=party,
        house_vote=(info["house_votes"] or [None])[-1],
        senate_vote=(info["senate_votes"] or [None])[-1],
        in_force=info["in_force"],
    )
    response.headers["Cache-Control"] = "public, max-age=900"
    return response


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

    debates = []
    for sp in reversed((info or {}).get("speeches", [])[-12:]):
        when = date.fromisoformat(sp["date"]) if sp["date"] else None
        debates.append({**sp, "when": when, "link": speech_link(sp, parl_session)})
    committees = [{**c, "link": None if c["senate"] else HOUSE_COMMITTEE_URL.format(acr=c["acr"]),
                   "page": None if c["senate"] else url_for("committee_page", acr=c["acr"]),
                   "first_d": date.fromisoformat(c["first"]) if c["first"] else None,
                   "last_d": date.fromisoformat(c["last"]) if c["last"] else None}
                  for c in (info or {}).get("committees", [])]

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
        timeline=build_timeline(bill) if bill else [],
        debates=debates,
        committees=committees,
        debates_url=OPENPARLIAMENT_BILL_URL.format(session=parl_session, number=number),
        share_text=(blocks[0]["text"] if blocks and blocks[0]["text"] else (bill["title"] if bill else ""))[:200],
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
    passed_bills, _ = recent_passed_bills(records, limit=10**6)
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
            "sponsors": top_sponsors(prows),
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
        monthly=monthly_laws(passed_bills),
        law_speed=time_to_law_summary(passed_bills),
        topics=topic_bars(rows),
        origin=origin_stats(records),
        recent=recent_introductions(records),
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


@app.route("/members")
def members_page():
    directory = get_directory()
    members = directory["members"]
    postal = request.args.get("postal", "").strip()[:12]
    lookup = find_my_mps(postal, members) if postal and members else None
    provinces = sorted({m["province"] for m in members if m["province"]})
    return render_template(
        "members.html",
        active_tab="members",
        page_width="max-w-4xl",
        groups=party_groups(members),
        party_colours=PARTY_COLOURS,
        member_total=len(members),
        provinces=provinces,
        has_contacts=directory["contacts"],
        section="house",
        error=directory["error"],
        postal=postal,
        lookup=lookup,
        export_url=url_for("export_members"),
        fetched_at=None,
        total=0,
    )


@app.route("/members/senate")
def senate_page():
    data = get_senators()
    senators = data["senators"]
    return render_template(
        "senate.html",
        active_tab="members",
        page_width="max-w-4xl",
        section="senate",
        groups=senate_groups(senators),
        member_total=len(senators),
        provinces=sorted({s["province"] for s in senators if s["province"]}),
        error=data["error"],
        official_url=SENATE_OFFICIAL_URL,
        fetched_at=None,
        total=0,
    )


@app.route("/committees")
def committees_page():
    return render_template(
        "committees.html",
        active_tab="members",
        page_width="max-w-4xl",
        section="committees",
        committees=get_committee_list(),
        list_url=COMMITTEE_LIST_URL,
        fetched_at=None,
        total=0,
    )


@app.route("/committees/<acr>")
def committee_page(acr: str):
    acr = acr.upper()
    if not re.match(r"^[A-Z]{3,6}$", acr):
        abort(404)
    data = get_committee(acr)
    by_id = {m["id"]: m for m in get_directory()["members"]}
    roster = {"Chair": [], "Vice-Chair": [], "Member": []}
    if data:
        for pid, role in data["people"]:
            if pid in by_id:
                roster.setdefault(role, []).append(by_id[pid])
    return render_template(
        "committee.html",
        active_tab="members",
        page_width="max-w-4xl",
        section="committees",
        acr=acr,
        name=(data or {}).get("name") or ("Standing Committee on " + COMMITTEE_NAMES[acr] if acr in COMMITTEE_NAMES else acr),
        roster=roster,
        roster_total=sum(len(v) for v in roster.values()),
        found=bool(data),
        official_url=HOUSE_COMMITTEE_URL.format(acr=acr),
        party_colours=PARTY_COLOURS,
        fetched_at=None,
        total=0,
    )


@app.route("/api/snapshot")
def snapshot_api():
    """Every bill's current status, so the browser can show what changed since the last visit."""
    records, _ = fetch_records()
    bills = {}
    for rec in records:
        bill = normalize(rec)
        if bill and not bill["pro_forma"] and bill["number_ok"]:
            bills[bill["number"].upper()] = {"s": bill["status"], "p": bill["session"],
                                             "t": (bill["short_title"] or bill["title"])[:90]}
    response = jsonify(bills=bills, count=len(bills))
    response.headers["Cache-Control"] = "public, max-age=300"
    return response


@app.route("/compare")
def compare():
    records, warning = fetch_records()
    bills = [b for b in (normalize(r) for r in records) if b and not b["pro_forma"] and b["number_ok"]]
    bills.sort(key=lambda b: bill_sort_key(b["number"]))
    by_number = {b["number"].upper(): b for b in bills}
    picks = [by_number.get(request.args.get(k, "").strip().upper()) for k in ("a", "b")]

    columns = []
    for bill in picks:
        if not bill:
            columns.append(None)
            continue
        info = fetch_bill_json(bill["session"], bill["number"].upper())
        party = None
        if info and info["sponsor_id"]:
            party = get_member_parties().get(info["sponsor_id"]) or canon_party(info["sponsor_caucus"] or "")
        summary = ""
        if info and info["summary_html"]:
            blocks, _ = blocks_from_legisinfo(info["summary_html"])
            summary = next((b["text"] for b in blocks if b["text"]), "")
        days_open = None
        if bill["introduced"] and not bill["passed"] and is_active(bill["status"]):
            days_open = (datetime.now(timezone.utc) - bill["introduced"]).days
        columns.append({"bill": bill, "info": info, "party": party, "summary": trim_text(summary, 380),
                        "vote": ((info or {}).get("house_votes") or [None])[-1], "days_open": days_open})
    def fmt(dt):
        return dt.strftime("%B %-d, %Y") if dt else "\u2014"

    def time_cell(c):
        bill = c["bill"]
        if bill["passed"]:
            extra = f" ({bill['days_to_law']} days from first reading)" if bill["days_to_law"] is not None else ""
            return f"Became law {fmt(bill['assent'])}{extra}"
        if c["days_open"] is not None:
            return f"{c['days_open']} days since it was introduced"
        return "\u2014"

    def sponsor_cell(c):
        info = c["info"]
        if not info or not info["sponsor_name"]:
            return "\u2014"
        return info["sponsor_name"] + (f", {c['party']}" if c["party"] else "")

    def vote_cell(c):
        vote = c["vote"]
        return f"{vote['yeas']} for, {vote['nays']} against" if vote else "\u2014"

    row_defs = (
        ("Status", lambda c: c["bill"]["status"] or "\u2014"),
        ("Type", lambda c: c["bill"]["type_label"]),
        ("Started in", lambda c: c["bill"]["chamber"]),
        ("Currently in", lambda c: c["bill"]["current_chamber"]),
        ("Introduced", lambda c: fmt(c["bill"]["introduced"])),
        ("Time", time_cell),
        ("Topic", lambda c: c["bill"]["topic"]),
        ("Amends", lambda c: ", ".join(c["bill"]["amends"]) or "\u2014"),
        ("Sponsor", sponsor_cell),
        ("Latest House vote", vote_cell),
        ("Summary", lambda c: c["summary"] or "\u2014"),
    )
    rows = [(label, [fn(c) if c else "" for c in columns]) for label, fn in row_defs] if all(columns) else []
    return render_template(
        "compare.html",
        active_tab=None,
        options=bills,
        columns=columns,
        rows=rows,
        selected=[b["number"] if b else "" for b in picks],
        stages=[label for label, _ in STAGES],
        warning=warning,
        fetched_at=_fetched_at(),
        total=len(records),
    )


@app.route("/glossary")
def glossary():
    return render_template("glossary.html", active_tab=None, terms=GLOSSARY, slugs=[_slug(t) for t, _ in GLOSSARY],
                           fetched_at=None, total=0)


@app.route("/export/active.csv")
def export_active():
    records, _ = fetch_records()
    chamber, kind, sort, q = _active_filters()
    return bills_csv(all_active_bills(records, chamber, kind, q, sort), "parltrack-active-bills.csv")


@app.route("/export/passed.csv")
def export_passed():
    records, _ = fetch_records()
    return bills_csv(recent_passed_bills(records, limit=10**6)[0], "parltrack-passed-bills.csv")


@app.route("/export/following.csv")
def export_following():
    wanted = [p.strip().upper() for p in request.args.get("b", "").split(",")[:60]
              if BILL_NUMBER_RE.match(p.strip())]
    records, _ = fetch_records()
    bills = [b for b in (normalize(r) for r in records) if b and b["number"].upper() in wanted]
    return bills_csv(bills, "parltrack-my-bills.csv")


@app.route("/export/members.csv")
def export_members():
    members = get_directory()["members"]
    header = ["Name", "Party", "Riding", "Province", "Email", "Ottawa phone", "Constituency phone",
              "Constituency address", "Website"]
    rows = [[m["name"], m["party"], m["riding"], m["province"], m["email"], m["hill_tel"], m["const_tel"],
             " | ".join(m["const_addr"]), m["website"]] for m in members]
    return csv_response("parltrack-members.csv", header, rows)


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
