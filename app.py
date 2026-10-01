"""Canadian parliamentary bill tracker.

Fetches the current-session bill list from LEGISinfo, keeps the 20 most
recently active bills that are still alive, and renders a 5-line breakdown
for each one.

Run:
    pip install flask requests
    python app.py
"""

from __future__ import annotations

import json
import os
import re
import time
from datetime import datetime, timezone

import requests
from flask import Flask, jsonify, render_template

LEGISINFO_URL = "https://www.parl.ca/legisinfo/en/bills/json"
CACHE_TTL_SECONDS = 300
TOP_N = 20

app = Flask(__name__)

# --------------------------------------------------------------------------
# Field mapping
#
# LEGISinfo changed the shape of this feed around Aug 13, 2026
# (BillNumberFormatted -> NumberCode, CurrentStatusEn -> StatusNameEn, ...).
# Each field below lists the known names for both shapes, newest first.
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

# Plain-language "what happens next", keyed on the stage text.
NEXT_STEPS = (
    ("third reading", "Final vote in this chamber; if it passes, it moves to the other chamber or to Royal Assent."),
    ("report stage", "Members consider committee amendments, then the bill goes to third reading."),
    ("committee", "Committee hears witnesses and reviews the text clause by clause, then reports back."),
    ("second reading", "Debate on the bill's principle, then a vote on whether to send it to committee."),
    ("first reading", "Formally introduced; it waits to be scheduled for second reading."),
    ("order of precedence", "A private member's bill that must be drawn for debate before it can advance."),
)

_cache: dict = {"fetched_at": 0.0, "records": None}


# --------------------------------------------------------------------------
# Fetching
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
# Parsing
# --------------------------------------------------------------------------
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


def build_breakdown(number: str, short: str, long: str, origin: str, current: str,
                    status: str, stage: str) -> list[dict]:
    """Exactly five labelled lines per bill, built from the feed's own fields."""
    where = (
        f"Introduced in the {origin}; currently in the {current}."
        if current != origin
        else f"Introduced in the {origin} and still there."
    )
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
    idx = stage_index(status)
    return {
        "number": number,
        "short_title": short,
        "title": long,
        "status": status,
        "chamber": origin,
        "current_chamber": current,
        "chamber_class": "senate" if current == "Senate" else "house",
        "stage_index": idx,
        "active_date": parse_date(pick(record, DATE_KEYS)),
        "breakdown": build_breakdown(number, short, long, origin, current, status, stage),
    }


def top_active_bills(records: list[dict], limit: int = TOP_N) -> list[dict]:
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


# --------------------------------------------------------------------------
# Routes
# --------------------------------------------------------------------------
@app.route("/")
def index():
    records, warning = fetch_records()
    bills = top_active_bills(records)
    if records and not bills and not warning:
        warning = ("The feed loaded, but no bills could be read from it. LEGISinfo may have "
                   "renamed its fields; open /debug to see the keys it returns.")
    return render_template(
        "index.html",
        bills=bills,
        stages=[label for label, _ in STAGES],
        warning=warning,
        total=len(records),
        fetched_at=datetime.fromtimestamp(_cache["fetched_at"]) if _cache["fetched_at"] else None,
    )


@app.route("/debug")
def debug():
    """Show the raw keys and first record, for adapting to schema changes."""
    # Only bypass the cache when running locally in debug mode, so a public
    # deployment can't be used to hammer LEGISinfo.
    records, warning = fetch_records(force=app.debug)
    return jsonify(
        warning=warning,
        record_count=len(records),
        keys=sorted(records[0].keys()) if records else [],
        first_record=records[0] if records else None,
    )


@app.route("/healthz")
def healthz():
    """Lightweight check for the hosting platform; makes no outside requests."""
    return "ok", 200


if __name__ == "__main__":
    # Local use: python3 app.py   (set FLASK_DEBUG=1 for auto-reload and verbose errors).
    # Hosted use goes through gunicorn (see render.yaml) and never reaches this block.
    app.run(debug=os.environ.get("FLASK_DEBUG") == "1", port=int(os.environ.get("PORT", 5000)))
