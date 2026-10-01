"""ParlTrack Canada: Canadian parliamentary bill tracker.

Pages
  /                              the 20 most recently active bills still moving
  /passed                        the 10 most recent bills with royal assent
  /summary/<session>/<number>    JSON: official 3-sentence summary of a bill
  /debug, /healthz               troubleshooting and hosting checks

Run locally:
    pip install -r requirements.txt
    python3 app.py
"""

from __future__ import annotations

import json
import os
import re
import threading
import time
from collections import Counter
from datetime import datetime, timezone
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


def get_summary(parl_session: str, number: str) -> str | None:
    key = (parl_session, number)
    now = time.time()
    with _summary_lock:
        hit = _summary_cache.get(key)
    if hit and now < hit["expires"]:
        return hit["summary"]

    summary = None
    for stage in SUMMARY_STAGES:
        text = _download_text(DOCUMENT_URL.format(session=parl_session, number=number, stage=stage))
        body = extract_summary(text) if text else None
        if body:
            summary = condense(body)
            break

    ttl = SUMMARY_TTL if summary else SUMMARY_FAIL_TTL
    with _summary_lock:
        _summary_cache[key] = {"summary": summary, "expires": now + ttl}
    return summary


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
