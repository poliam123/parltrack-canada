"""Federal lobbying data from the Office of the Commissioner of Lobbying of Canada.

The Commissioner publishes two ZIP files of CSVs every week (open data, see LICENCE_URL):
  * registrations: who is registered to lobby, for whom, on what, and who does the lobbying
  * monthly communication reports: each oral, arranged meeting with a designated public
    office holder (ministers, MPs, senators, their senior staff and senior officials)

The CSVs are Windows-1252 text, every field is quoted, the word "null" means empty, and some
descriptions contain line breaks. build_database() streams both files into one SQLite file,
keeping only what PolitiKit shows:
  * communication reports since LOBBY_SINCE (the opening of the 44th Parliament), with the
    officials met, subject areas and (from October 2024) the lobbyist's own description;
  * registrations in effect at any time since LOBBY_SINCE, with full details for active ones;
  * links from officials to sitting MPs (MPMatcher) and from descriptions to bills (BillResolver).

Nothing in this file uses Flask, so it can be tested on its own. If the Commissioner renames a
column, the build stops with a message naming the file and listing the columns it found.
"""

from __future__ import annotations

import csv
import io
import os
import re
import sqlite3
import tempfile
import time
import unicodedata
import zipfile
from collections import Counter, defaultdict
from datetime import date, datetime, timedelta

import requests

# --------------------------------------------------------------------------
# Sources
# --------------------------------------------------------------------------
REGISTRATIONS_URL = os.environ.get(
    "LOBBY_REGISTRATIONS_URL",
    "https://lobbycanada.gc.ca/media/zwcjycef/registrations_enregistrements_ocl_cal.zip")
COMMUNICATIONS_URL = os.environ.get(
    "LOBBY_COMMUNICATIONS_URL",
    "https://lobbycanada.gc.ca/media/mqbbmaqk/communications_ocl_cal.zip")
OPEN_DATA_PAGE = "https://lobbycanada.gc.ca/en/open-data/"
LICENCE_URL = "https://lobbycanada.gc.ca/en/open-data/open-data-licence-agreement/"
ATTRIBUTION = ("Contains information licensed under the Open Data Licence Agreement — "
               "Office of the Commissioner of Lobbying.")
REPORT_URL = "https://lobbycanada.gc.ca/app/secure/ocl/lrs/do/cmmLgPblcVw?comlogId={id}"
REGISTRY_SEARCH_URL = "https://lobbycanada.gc.ca/app/secure/ocl/lrs/do/advSrch"
HTTP_HEADERS = {"User-Agent": "PolitiKit/1.0 (+https://politikit.ca)"}

# Sessions of Parliament covered, newest first: (code, first sitting day, last day or None).
SESSIONS = (
    ("45-1", date(2025, 5, 26), None),
    ("44-1", date(2021, 11, 22), date(2025, 1, 6)),
)
CURRENT = SESSIONS[0]
LOBBY_SINCE = SESSIONS[-1][1]

SCHEMA_VERSION = "3"
DB_PATH = os.environ.get("LOBBY_DB", os.path.join(tempfile.gettempdir(), "politikit-lobbying.sqlite3"))

REG_TYPES = {1: "Consultant", 2: "In-house (corporation)", 3: "In-house (organization)"}
ORG_KINDS = {1: "Client of a consultant lobbyist", 2: "Corporation", 3: "Organization"}

csv.field_size_limit(16 * 1024 * 1024)


class SchemaError(RuntimeError):
    """A file in the ZIP is missing, or a column was renamed."""


# --------------------------------------------------------------------------
# Small text helpers
# --------------------------------------------------------------------------
def clean(value) -> str:
    value = (value or "").strip()
    return "" if value.lower() == "null" else value


def fold(text: str) -> str:
    """Lower case, no accents, straight apostrophes, single spaces."""
    text = unicodedata.normalize("NFKD", text or "")
    text = "".join(c for c in text if not unicodedata.combining(c))
    text = text.replace("’", "'").replace("‘", "'").replace("‑", "-").replace("–", "-")
    return re.sub(r"\s+", " ", text).strip().lower()


def to_int(value) -> int | None:
    value = clean(value)
    return int(value) if value.isdigit() else None


def iso_date(value) -> str:
    """'2026-10-30' from the feed's dates (some carry a time part); '' if missing."""
    value = clean(value)[:10]
    return value if re.fullmatch(r"\d{4}-\d{2}-\d{2}", value) else ""


def nice_case(name: str) -> str:
    """'JENNERY' -> 'Jennery'; names already in mixed case are left alone."""
    name = re.sub(r"\s+", " ", name or "").strip()
    if not name or name != name.upper() or not re.search(r"[A-Z]", name):
        return name

    def word(w: str) -> str:
        w = w.lower()
        w = "-".join(p[:1].upper() + p[1:] for p in w.split("-"))
        w = re.sub(r"^(Mc|O')([a-z])", lambda m: m.group(1) + m.group(2).upper(), w)
        return w
    return " ".join(word(w) for w in name.split(" "))


def person(first: str, last: str) -> str:
    return re.sub(r"\s+", " ", f"{nice_case(clean(first))} {nice_case(clean(last))}").strip()


def org_name(en: str, fr: str) -> str:
    return clean(en) or clean(fr)


# --------------------------------------------------------------------------
# Reading the ZIPs
# --------------------------------------------------------------------------
def _member(zf: zipfile.ZipFile, name: str) -> str:
    wanted = name.lower()
    for info in zf.infolist():
        if info.filename.replace("\\", "/").rsplit("/", 1)[-1].lower() == wanted:
            return info.filename
    raise SchemaError(f"{name} is missing from the ZIP (it has: {', '.join(zf.namelist())})")


def read_rows(zf: zipfile.ZipFile, name: str, columns: tuple, optional: tuple = ()):
    """Yield one tuple per CSV row with the requested columns, cleaned. Each column may be a
    tuple of alternative names. Optional columns come back as '' when absent."""
    member = _member(zf, name)
    with zf.open(member) as raw:
        text = io.TextIOWrapper(raw, encoding="cp1252", errors="replace", newline="")
        reader = csv.reader(text)
        try:
            header = [h.strip().lstrip("﻿").upper() for h in next(reader)]
        except StopIteration:
            return
        where = {h: i for i, h in enumerate(header)}

        def locate(spec, required):
            for alt in (spec if isinstance(spec, tuple) else (spec,)):
                if alt.upper() in where:
                    return where[alt.upper()]
            if required:
                raise SchemaError(f"{name}: column {spec} not found (columns: {', '.join(header)})")
            return None

        idx = [locate(c, True) for c in columns] + [locate(c, False) for c in optional]
        width = len(header)
        for row in reader:
            if len(row) < width:
                row = row + [""] * (width - len(row))
            yield tuple(clean(row[i]) if i is not None else "" for i in idx)


# --------------------------------------------------------------------------
# Matching officials to sitting MPs
# --------------------------------------------------------------------------
HONORIFICS = re.compile(
    r"\b(?:the\s+)?(?:right\s+)?(?:hon(?:ourable|orable)?|l'honorable|honorable)\b\.?|"
    r"\b(?:p\.\s?c\.|c\.\s?p\.|m\.\s?p\.|k\.\s?c\.|q\.\s?c\.)|\bp\.c\b|\bm\.p\b|\bmp\b|\bpc\b|\bdr\b\.?|\bmrs?\b\.?|\bms\b\.?",
    re.IGNORECASE)
ROLE_CLEANUP = re.compile(
    r"(?:associate |assistant |senior associate )?deputy minister|sous-ministr\w*|vice-premi\w*|"
    r"(?:to|of|for) the (?:prime )?minister|du (?:premier )?ministre|de la ministre|office of the minister|"
    r"cabinet du (?:premier )?ministre|minister'?s office|ministerial", re.IGNORECASE)
MP_ROLE = re.compile(
    r"member of par|parli?a?ment|parlement|\bmp\b|\bm\.p\.|d[ée]put[ée]|\bminist(?:er|re)\b|secretary of state|"
    r"secr[ée]taire d.[ée]tat|parliamentary secretary|secr[ée]taire parlementaire|prime minister|"
    r"premier ministre|\bleader\b|chef de l|speaker|pr[ée]sident de la chambre|\bwhip\b|critic|porte-parole|"
    r"privy council|conseil priv[ée]|\bchair\b|vice-chair",
    re.IGNORECASE)
STAFF_ROLE = re.compile(
    r"deputy minister|sous-minist|assistant|adjoint|advis|conseill|director|directeur|directrice|"
    r"chief of staff|chef de cabinet|officer|agent|analyst|manager|gestionnaire|coordinat|clerk|greffi|"
    r"\bstaff|employ|executive|stagiaire|intern\b|research|recherch|counsel|liaison|"
    r"\bsecretary\b(?! of state)|attach[ée]|associate|lead\b|head of|commissioner|ambassador",
    re.IGNORECASE)


def _name_tokens(text: str) -> list[str]:
    text = HONORIFICS.sub(" ", text or "")
    text = fold(text)
    return [t for t in re.split(r"[^a-z]+", text) if len(t) > 1]


class MPMatcher:
    """Links an official named in a communication report to a sitting MP.

    The name must match (accents, case, honorifics, middle initials and the split between
    first and last names don't matter). A looser match on a unique surname plus the same first
    initial is accepted only when the title describes an elected role. Titles that describe staff
    or public servants ('Deputy Minister', 'Policy Advisor') never match by surname alone, and
    rule out a full-name match unless the title also names an elected role."""

    def __init__(self, members: list[dict]):
        self.by_key: dict[str, int] = {}
        self.by_last: dict[str, list[tuple[int, str]]] = defaultdict(list)
        for m in members or []:
            pid = m.get("id")
            first, last = m.get("first") or "", m.get("last") or ""
            if not pid or not (first or last):
                continue
            key = "".join(_name_tokens(f"{first} {last}"))
            self.by_key.setdefault(key, pid)
            last_key = "".join(_name_tokens(last))
            first_tokens = _name_tokens(first)
            self.by_last[last_key].append((pid, first_tokens[0] if first_tokens else ""))
        self._cache: dict[tuple, int | None] = {}

    def match(self, first: str, last: str, title: str = "", institution: str = "") -> int | None:
        cache_key = (first, last, title, institution)
        if cache_key in self._cache:
            return self._cache[cache_key]
        result = self._match(first, last, title, institution)
        if len(self._cache) < 200_000:
            self._cache[cache_key] = result
        return result

    def _match(self, first, last, title, institution):
        title = title or ""
        role_text = ROLE_CLEANUP.sub(" ", title)
        elected = bool(MP_ROLE.search(role_text)) or bool(re.search(r"house of commons|chambre des communes", title, re.I) and not STAFF_ROLE.search(title))
        staff = bool(STAFF_ROLE.search(title)) and not MP_ROLE.search(role_text)
        in_house = bool(re.search(r"house of commons|chambre des communes", institution or "", re.I))

        first_t, last_t = _name_tokens(first), _name_tokens(last)
        if not last_t and not first_t:
            return None
        key = "".join(first_t + last_t)
        pid = self.by_key.get(key)
        if pid is None and len(first_t) > 1:  # "Michael D." already handled; try first given name only
            pid = self.by_key.get("".join(first_t[:1] + last_t))
        if pid is not None:
            if staff:
                return None
            return pid

        # Surname unique among sitting MPs, same first initial, and an elected-role title.
        if not elected or not last_t or not first_t:
            return None
        candidates = self.by_last.get("".join(last_t), [])
        if len(candidates) == 1 and candidates[0][1][:1] == first_t[0][:1]:
            return candidates[0][0]
        if in_house and len(candidates) > 1:
            same = [c for c in candidates if c[1] and c[1] == first_t[0]]
            if len(same) == 1:
                return same[0][0]
        return None


# --------------------------------------------------------------------------
# Finding bills in the lobbyists' own descriptions
#
# Bill numbers restart every session, and lobbyists often keep writing "Bill C-27" or
# "Bill C-11" long after the bill died or became law, so a number alone isn't enough.
# Each mention is scored against every session's bill with that number using the words and
# act names in its titles (English and French), years and phrases like "formerly" or
# "the last Parliament". Only when nothing in the text points anywhere does the number fall
# back to the bill of the session sitting on the date of the report, and never when the
# text names a different act. Mentions that stay unclear are not linked.
# --------------------------------------------------------------------------
MENTION_RE = re.compile(
    r"\b(?:bill|projet\s+de\s+loi|pl)\s+(?:no\.?\s*|n[oº°]\.?\s*)?([CcSs])\s?[-‐‑‒–—]?\s?(\d{1,4})\b",
    re.IGNORECASE)
BARE_RE = re.compile(r"(?<![\w/.-])([CS])-(\d{1,4})\b(?![-/]\d)")
YEAR_RE = re.compile(r"\b(19[5-9]\d|20[0-4]\d)\b")
PARLIAMENT_RE = re.compile(r"\b(4\d)(?:st|nd|rd|th|e|i[eè]me)\s+(?:parliament|parlement|l[ée]gislature)", re.IGNORECASE)
PREVIOUS_RE = re.compile(
    r"\b(?:last|previous|prior|former)\s+(?:parliament|session)|l[ée]gislature\s+pr[ée]c[ée]dente|derni[eè]re\s+l[ée]gislature",
    re.IGNORECASE)
HISTORIC_RE = re.compile(r"\bformer(?:ly)?\b|\bprevious(?:ly)?\b|\bancien(?:ne|nement)?\b|\bpost\b|\bnow\s+(?:called|known)", re.IGNORECASE)
NAMED_ACT_RE = re.compile(r"\b(?:act|acts|loi|lois|code)\b", re.IGNORECASE)
STOPWORDS = set("""
act acts bill bills canada canadian canadians amend amends amending amendment amendments related
consequential certain respecting respect enact enacting make making other another measure measures
provision provisions implement implementing implementation establish establishing with that this from
into their there which parliament tabled also part parts section give effect purpose purposes
loi lois projet modifiant modifier visant concernant certaines certains mesures autres autre apportant
modifications modification connexes correlatives edictant edicter matiere relative relatives relatif
canadien canadienne canadiens canadiennes dans pour avec sont cette leur leurs mise oeuvre deposee
""".split())


def _tokens(text: str) -> set[str]:
    return {w for w in re.findall(r"[a-z]{4,}", fold(text)) if w not in STOPWORDS}


def _strip_title_suffix(title: str) -> str:
    title = (title or "").strip()
    for _ in range(3):
        title = re.sub(r",?\s*(?:No\.?|no|n[oº])\s*\d+\s*$|,?\s*\(?\d{4}(?:-\d{2})?\)?\s*$", "", title).strip()
    return title


def title_phrases(short: str, long: str, short_fr: str = "", long_fr: str = "") -> list[str]:
    """Distinctive phrases: the short titles and the names of acts the bill would enact."""
    out = []
    for s in (short, short_fr):
        s = _strip_title_suffix(s)
        if len(s) >= 8:
            out.append(fold(s))
    m = re.search(r"\bto enact (?:the )?(.+?)(?:,? and to |,? and make |, to |\.|$)", long or "", re.IGNORECASE)
    if m:
        for part in re.split(r",\s*(?:and\s+)?(?:the\s+)?|\s+and\s+the\s+", m.group(1)):
            part = _strip_title_suffix(part.strip(" ."))
            if len(part) >= 10 and part.lower().endswith("act"):
                out.append(fold(part))
    m = re.search(r"\b[ée]dictant (?:la |le |les )?(.+?)(?:,? et (?:modifiant|apportant|à|a) |,? et à |\.|$)", long_fr or "", re.IGNORECASE)
    if m:
        for part in re.split(r",\s*(?:la|le|les)\s+|\s+et\s+(?:la|le|les)\s+", m.group(1)):
            part = _strip_title_suffix(part.strip(" ."))
            if len(part) >= 10 and fold(part).startswith("loi"):
                out.append(fold(part))
    seen, phrases = set(), []
    for p in out:
        p = re.sub(r"^(?:the|la|le|les)\s+", "", p)
        if p not in seen and not re.fullmatch(r"(?:an )?act to amend.*|loi modifiant.*", p):
            seen.add(p)
            phrases.append(p)
    # Lobbyists often paste the long title itself; its opening words are distinctive enough
    # once they run past the generic "An Act to amend the Criminal Code".
    for long_t in (long, long_fr):
        opening = fold(long_t or "")[:55].rsplit(" ", 1)[0]
        if len(opening) >= 40 and opening not in seen:
            seen.add(opening)
            phrases.append(opening)
    return phrases


def _session_bounds(code: str) -> tuple[date, date]:
    for c, start, end in SESSIONS:
        if c == code:
            return start, end or date.max
    return date.min, date.max


def session_on(day: date) -> str | None:
    for code, start, end in SESSIONS:
        if start <= day and (end is None or day <= end):
            return code
    return None


def find_mentions(text: str) -> list[tuple[str, int, int, str]]:
    """(number like 'C-27', start, end, 'bill' or 'bare') for each bill number in the text."""
    found = []
    for m in MENTION_RE.finditer(text or ""):
        found.append((f"{m.group(1).upper()}-{int(m.group(2))}", m.start(), m.end(), "bill"))
    taken = [(s, e) for _, s, e, _ in found]
    for m in BARE_RE.finditer(text or ""):
        if any(s <= m.start() < e for s, e in taken):
            continue
        found.append((f"{m.group(1)}-{int(m.group(2))}", m.start(), m.end(), "bare"))
    found.sort(key=lambda t: t[1])
    return found


DETAILS_HEADING = re.compile(r"\s*\n\s*(?:Details|D[ée]tails)\s*:\s*", re.IGNORECASE)


def snippet_around(text: str, start: int, end: int, before: int = 90, after: int = 170) -> str:
    """The lobbyist's words around a mention, cut at whole words, headings tidied."""
    a, b = max(0, start - before), min(len(text), end + after)
    seg = text[a:b]
    if a > 0 and len(seg.split(None, 1)) > 1:
        seg = seg.split(None, 1)[1]          # drop the partial first word
    if b < len(text) and len(seg.rsplit(None, 1)) > 1:
        seg = seg.rsplit(None, 1)[0]         # and the partial last one
    seg = DETAILS_HEADING.sub(" — ", seg)
    seg = re.sub(r"^\s*(?:Details|D[ée]tails)\s*:\s*", "", seg, flags=re.IGNORECASE)
    seg = re.sub(r"\s+", " ", seg).strip(" —–-:;,")
    return ("…" if a > 0 else "") + seg + ("…" if b < len(text) else "")


class BillResolver:
    """Decides which session's bill a mention like 'Bill C-27' refers to.

    bills: dicts with session ('45-1'), number ('C-27'), short_title, title, and optionally
    short_title_fr, title_fr, introduced (date)."""

    def __init__(self, bills: list[dict]):
        self.by_number: dict[str, list[dict]] = defaultdict(list)
        sessions = set()
        for b in bills or []:
            number = (b.get("number") or "").upper()
            session = b.get("session") or ""
            if not re.fullmatch(r"[CS]-\d+", number) or session not in {s[0] for s in SESSIONS}:
                continue
            sessions.add(session)
            self.by_number[number].append({
                "session": session, "number": number,
                "tokens": _tokens(" ".join(filter(None, (b.get("short_title"), b.get("title"),
                                                         b.get("short_title_fr"), b.get("title_fr"))))),
                "phrases": title_phrases(b.get("short_title", ""), b.get("title", ""),
                                         b.get("short_title_fr", ""), b.get("title_fr", "")),
                "introduced": b.get("introduced"),
                "label": b.get("short_title") or b.get("title") or "",
            })
        # Without every session's bill list, a bare number can't safely fall back to the
        # sitting session: it might be an old bill we can't see.
        self.complete = sessions >= {s[0] for s in SESSIONS}

    def evidence(self, number: str, window: str, when: date | None) -> tuple[str | None, str]:
        """(session, how) from the words near the mention; (None, reason) if nothing points anywhere."""
        candidates = list(self.by_number.get(number, []))
        if not candidates:
            return None, "unknown"
        folded = fold(window)
        if when:
            candidates = [c for c in candidates
                          if not c["introduced"] or c["introduced"] <= when + timedelta(days=3)]
        if not candidates:
            return None, "not-yet"

        # Explicit session, e.g. "Bill C-8 (45-1)" or "in the 44th Parliament".
        sess_hint = None
        m = re.search(re.escape(number[2:]) + r"\W{0,3}\(\s*(4\d)\s*[-–]\s*([1-4])\s*\)", window)
        if m:
            sess_hint = f"{m.group(1)}-{m.group(2)}"
        else:
            m = PARLIAMENT_RE.search(window)
            if m:
                sess_hint = m.group(1) + "-"
        if sess_hint:
            narrowed = [c for c in candidates if c["session"].startswith(sess_hint)]
            if len(narrowed) == 1:
                return narrowed[0]["session"], "session"
            if not narrowed:
                return None, "other-session"
        if PREVIOUS_RE.search(window) and when:
            sitting = session_on(when)
            narrowed = [c for c in candidates if c["session"] != sitting]
            if len(narrowed) == 1:
                return narrowed[0]["session"], "previous"
            candidates = narrowed or candidates

        # Years: "enacted by Bill C-69 in 2019" can't be a bill from these sessions.
        years = {int(y) for y in YEAR_RE.findall(window)}
        if years:
            def overlaps(c):
                start, end = _session_bounds(c["session"])
                return any(start.year <= y <= (end.year if end != date.max else 9999) for y in years)
            narrowed = [c for c in candidates if overlaps(c)]
            if not narrowed:
                return None, "other-year"
            candidates = narrowed

        # Titles: phrases count for much more than single words.
        context_tokens = _tokens(window)
        scored = []
        for c in candidates:
            score = sum(10 for p in c["phrases"] if p and p in folded)
            score += len(c["tokens"] & context_tokens)
            scored.append((score, c))
        scored.sort(key=lambda t: -t[0])
        best, top = scored[0]
        second = scored[1][0] if len(scored) > 1 else 0
        enough = best >= 2 or (best >= 1 and len(top["tokens"]) <= 2)
        if enough and best > second:
            return top["session"], "title"
        if years and len(candidates) == 1 and best >= 0 and len(years) and not NAMED_ACT_RE.search(folded):
            return candidates[0]["session"], "year"
        return None, "unclear"

    def fallback(self, number: str, window: str, when: date | None, kind: str) -> str | None:
        """The sitting session's bill, when the text gives no reason to think otherwise."""
        if kind != "bill" or not when or not self.complete:
            return None
        if HISTORIC_RE.search(window) or PREVIOUS_RE.search(window):
            return None
        bare = re.sub(r"projet\s+de\s+loi", " ", window, flags=re.IGNORECASE)
        if NAMED_ACT_RE.search(bare):
            return None
        if YEAR_RE.search(window):
            return None
        sitting = session_on(when)
        for c in self.by_number.get(number, []):
            if c["session"] == sitting and (not c["introduced"] or c["introduced"] <= when):
                return sitting
        return None

    def label(self, session: str, number: str) -> str:
        for c in self.by_number.get(number, []):
            if c["session"] == session:
                return c["label"]
        return ""


class MentionFinder:
    """find_mentions plus the text around each one, computed once per distinct description:
    registrations repeat the same text in every version, and lobbyists reuse descriptions."""

    def __init__(self):
        self._cache: dict[int, list[tuple[str, str, str, str]]] = {}

    def __call__(self, text: str) -> list[tuple[str, str, str, str]]:
        """[(number, window, snippet, kind)]"""
        if not text or not re.search(r"[CS]\s?-?\s?\d", text, re.IGNORECASE):
            return []
        key = hash(text)
        hit = self._cache.get(key)
        if hit is not None:
            return hit
        found = find_mentions(text)
        out = [(number, mention_window(text, found, i), snippet_around(text, s, e), kind)
               for i, (number, s, e, kind) in enumerate(found)]
        if out and len(self._cache) < 100_000:
            self._cache[key] = out
        return out


def mention_window(text: str, mentions: list, i: int) -> str:
    """Text around mention i, stopping at the neighbouring mentions so titles don't bleed across."""
    _, start, end, _ = mentions[i]
    prev_end = mentions[i - 1][2] if i > 0 else 0
    next_start = mentions[i + 1][1] if i + 1 < len(mentions) else len(text)
    before = text[max(prev_end, start - 90):start]
    after = text[end:min(next_start, end + 220)]
    return f"{before} {text[start:end]} {after}"


def resolve_all(items: list[dict], resolver: BillResolver) -> list[dict]:
    """items: {client, number, window, when, kind, ...}. Adds 'session' and 'how' (or drops the item).

    Three passes: evidence in the text; then the same organization's other mentions of that
    number (an organization that wrote "Bill C-27, Digital Charter" elsewhere means the same bill
    when it writes just "Bill C-27"); then the sitting session as a last resort."""
    by_org: dict[tuple, Counter] = defaultdict(Counter)
    pending = []
    for it in items:
        session, how = resolver.evidence(it["number"], it["window"], it["when"])
        it["session"], it["how"] = session, how
        if session:
            by_org[(it["client"], it["number"])][session] += 1
        else:
            pending.append(it)
    for it in pending:
        if it["how"] in ("other-year", "other-session", "unknown", "not-yet"):
            continue
        votes = by_org.get((it["client"], it["number"]))
        if votes:
            session, n = votes.most_common(1)[0]
            if n >= 1 and (len(votes) == 1 or n > sum(votes.values()) - n):
                it["session"], it["how"] = session, "organization"
                continue
        session = resolver.fallback(it["number"], it["window"], it["when"], it["kind"])
        if session:
            it["session"], it["how"] = session, "date"
    return [it for it in items if it.get("session")]


# --------------------------------------------------------------------------
# Downloading
# --------------------------------------------------------------------------
def _find_current_link(kind: str) -> str | None:
    """If a ZIP's address changes, find the new one on the open data page."""
    try:
        resp = requests.get(OPEN_DATA_PAGE, timeout=30, headers=HTTP_HEADERS)
        resp.raise_for_status()
    except requests.RequestException:
        return None
    pattern = r'href="([^"]*%s[^"]*\.zip)"' % ("registrations" if kind == "registrations" else "communications")
    m = re.search(pattern, resp.text, re.IGNORECASE)
    return requests.compat.urljoin(OPEN_DATA_PAGE, m.group(1)) if m else None


def download(url: str, dest: str, progress=None, kind: str = "") -> dict:
    """Stream a ZIP to dest. Returns {'url', 'modified', 'bytes'}; raises RuntimeError on failure."""
    def fetch(u):
        return requests.get(u, timeout=(20, 120), stream=True, headers=HTTP_HEADERS)

    try:
        resp = fetch(url)
        if resp.status_code == 404 and kind:
            new_url = _find_current_link(kind)
            if new_url and new_url != url:
                resp.close()
                url, resp = new_url, fetch(new_url)
        resp.raise_for_status()
    except requests.RequestException as exc:
        raise RuntimeError(f"Could not download {url} ({exc})") from exc
    total = int(resp.headers.get("Content-Length") or 0)
    got = 0
    with resp, open(dest, "wb") as out:
        first = True
        for chunk in resp.iter_content(1 << 20):
            if first:
                if not chunk.startswith(b"PK"):
                    raise RuntimeError(
                        f"{url} did not return a ZIP file (status {resp.status_code}). "
                        "The site may be blocking automated downloads.")
                first = False
            out.write(chunk)
            got += len(chunk)
            if progress:
                progress(got, total)
    if got < 1000:
        raise RuntimeError(f"{url} returned an empty file")
    return {"url": url, "modified": resp.headers.get("Last-Modified", ""), "bytes": got}


def remote_modified(url: str) -> str | None:
    """Last-Modified of a ZIP without downloading it, or None if the server won't say."""
    try:
        resp = requests.head(url, timeout=20, headers=HTTP_HEADERS, allow_redirects=True)
        if resp.status_code >= 400:
            return None
        return resp.headers.get("Last-Modified") or None
    except requests.RequestException:
        return None


# --------------------------------------------------------------------------
# Building the database
# --------------------------------------------------------------------------
SCHEMA = """
CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE subject (code TEXT PRIMARY KEY, name TEXT);
CREATE TABLE comm (id INTEGER PRIMARY KEY, client_num INTEGER, client TEXT, registrant_num INTEGER,
                   registrant TEXT, comm_date TEXT, reg_type INTEGER, posted TEXT);
CREATE TABLE comm_official (comm_id INTEGER, name TEXT, title TEXT, institution TEXT, branch TEXT, mp_id INTEGER);
CREATE TABLE comm_subject (comm_id INTEGER, code TEXT, custom TEXT);
CREATE TABLE comm_detail (comm_id INTEGER, codes TEXT, description TEXT);
CREATE TABLE reg (id INTEGER PRIMARY KEY, reg_type INTEGER, reg_num TEXT, firm TEXT, registrant_num INTEGER,
                  registrant TEXT, position TEXT, profile_id INTEGER, client_num INTEGER, client TEXT,
                  effective TEXT, end_date TEXT, posted TEXT, active INTEGER, gov_funding TEXT,
                  contingency TEXT, parent TEXT, coalition TEXT, subsidiary TEXT);
CREATE TABLE reg_detail (reg_id INTEGER, categories TEXT, codes TEXT, description TEXT);
CREATE TABLE reg_subject (reg_id INTEGER, code TEXT, custom TEXT);
CREATE TABLE reg_institution (reg_id INTEGER, institution TEXT);
CREATE TABLE lobbyist (reg_id INTEGER, lobbyist_id INTEGER, name TEXT, position TEXT,
                       former_dpoh INTEGER, former_poh INTEGER, kind TEXT);
CREATE TABLE public_office (lobbyist_id INTEGER, title TEXT, branch TEXT, institution TEXT,
                            start TEXT, end_date TEXT, dpoh INTEGER, details TEXT);
CREATE TABLE bill_mention (source TEXT, ref_id INTEGER, client_num INTEGER, session TEXT, number TEXT,
                           mention_date TEXT, snippet TEXT, how TEXT);
CREATE TABLE org (num INTEGER PRIMARY KEY, name TEXT, fold TEXT, kind INTEGER, reports INTEGER,
                  reports_now INTEGER, mp_reports INTEGER, first_date TEXT, last_date TEXT, active_regs INTEGER);
CREATE TABLE registrant (num INTEGER PRIMARY KEY, name TEXT, fold TEXT, firm TEXT, kind INTEGER, position TEXT,
                         reports INTEGER, reports_now INTEGER, last_date TEXT, active_regs INTEGER,
                         lobbyist_id INTEGER);
"""

INDEXES = """
CREATE INDEX comm_date_i ON comm(comm_date);
CREATE INDEX comm_client_i ON comm(client_num, comm_date);
CREATE INDEX comm_registrant_i ON comm(registrant_num, comm_date);
CREATE INDEX official_comm_i ON comm_official(comm_id);
CREATE INDEX official_mp_i ON comm_official(mp_id, comm_id);
CREATE INDEX official_inst_i ON comm_official(institution);
CREATE INDEX csubject_comm_i ON comm_subject(comm_id);
CREATE INDEX csubject_code_i ON comm_subject(code, comm_id);
CREATE INDEX cdetail_comm_i ON comm_detail(comm_id);
CREATE INDEX reg_client_i ON reg(client_num, active);
CREATE INDEX reg_registrant_i ON reg(registrant_num, active);
CREATE INDEX rdetail_i ON reg_detail(reg_id);
CREATE INDEX rsubject_i ON reg_subject(reg_id);
CREATE INDEX rinst_i ON reg_institution(reg_id);
CREATE INDEX lobbyist_reg_i ON lobbyist(reg_id);
CREATE INDEX office_i ON public_office(lobbyist_id);
CREATE INDEX mention_bill_i ON bill_mention(session, number);
CREATE INDEX mention_client_i ON bill_mention(client_num);
CREATE INDEX org_fold_i ON org(fold);
CREATE INDEX registrant_fold_i ON registrant(fold);
"""

BATCH = 5000


class _Writer:
    def __init__(self, conn: sqlite3.Connection, sql: str):
        self.conn, self.sql, self.rows, self.count = conn, sql, [], 0

    def add(self, row):
        self.rows.append(row)
        if len(self.rows) >= BATCH:
            self.flush()

    def flush(self):
        if self.rows:
            self.conn.executemany(self.sql, self.rows)
            self.count += len(self.rows)
            self.rows = []


def _ymd(value: str) -> date | None:
    try:
        return date.fromisoformat(value) if value else None
    except ValueError:
        return None


def build_database(reg_zip: str, comm_zip: str, out_path: str, members: list[dict] | None = None,
                   bills: list[dict] | None = None, since: date = LOBBY_SINCE, today: date | None = None,
                   progress=None, meta: dict | None = None) -> dict:
    """Read both ZIPs into a new SQLite file at out_path (written beside it, then swapped in).
    Returns counts for the meta table and logs."""
    today = today or date.today()
    since_s = since.isoformat()
    now_s = CURRENT[1].isoformat()
    say = progress or (lambda label, done=0, total=0: None)
    tmp = out_path + ".building"
    for leftover in (tmp, tmp + "-journal"):
        if os.path.exists(leftover):
            os.remove(leftover)
    conn = sqlite3.connect(tmp)
    conn.execute("PRAGMA journal_mode=OFF")
    conn.execute("PRAGMA synchronous=OFF")
    conn.executescript(SCHEMA)
    matcher = MPMatcher(members or [])
    resolver = BillResolver(bills or [])
    stats: dict = {}
    started = time.time()

    with zipfile.ZipFile(comm_zip) as cz, zipfile.ZipFile(reg_zip) as rz:
        # ---- Subject areas (the same list is in both files) ----
        for zf in (cz, rz):
            try:
                for code, en in read_rows(zf, "Codes_SubjectMatterTypesExport.csv", ("SUBJECT_CODE_OBJET", "SMT_EN_DESC")):
                    conn.execute("INSERT OR REPLACE INTO subject VALUES (?, ?)", (code, en))
                break
            except SchemaError:
                continue
        subjects = dict(conn.execute("SELECT code, name FROM subject"))

        # ---- Communication reports ----
        say("Reading communication reports")
        comm_w = _Writer(conn, "INSERT INTO comm VALUES (?,?,?,?,?,?,?,?)")
        keep: dict[int, tuple[int, str]] = {}   # id -> (client_num, comm_date)
        superseded = set()
        for (cid, cnum, en, fr, rnum, rlast, rfirst, cdate, rtype, posted, prev) in read_rows(
                cz, "Communication_PrimaryExport.csv",
                ("COMLOG_ID", "CLIENT_ORG_CORP_NUM", "EN_CLIENT_ORG_CORP_NM_AN", "FR_CLIENT_ORG_CORP_NM",
                 "REGISTRANT_NUM_DECLARANT", "RGSTRNT_LAST_NM_DCLRNT", "RGSTRNT_1ST_NM_PRENOM_DCLRNT",
                 "COMM_DATE", "REG_TYPE_ENR", "POSTED_DATE_PUBLICATION", "PREV_COMLOG_ID_PRECEDNT")):
            if prev.isdigit():
                superseded.add(int(prev))
            cdate = iso_date(cdate)
            if not cid.isdigit() or not cdate or cdate < since_s or cdate > today.isoformat():
                continue
            cid_i, cnum_i = int(cid), to_int(cnum)
            keep[cid_i] = (cnum_i, cdate)
            comm_w.add((cid_i, cnum_i, org_name(en, fr), to_int(rnum), person(rfirst, rlast), cdate,
                        to_int(rtype), iso_date(posted)))
        comm_w.flush()
        for old in superseded & keep.keys():
            conn.execute("DELETE FROM comm WHERE id = ?", (old,))
            keep.pop(old, None)
        stats["reports"] = len(keep)
        say("Reading officials met", 1, 4)

        off_w = _Writer(conn, "INSERT INTO comm_official VALUES (?,?,?,?,?,?)")
        matched = 0
        for (cid, last, first, title, branch, other, inst) in read_rows(
                cz, "Communication_DpohExport.csv",
                ("COMLOG_ID", "DPOH_LAST_NM_TCPD", "DPOH_FIRST_NM_PRENOM_TCPD", "DPOH_TITLE_TITRE_TCPD",
                 "BRANCH_UNIT_DIRECTION_SERVICE", "OTHER_INSTITUTION_AUTRE", "INSTITUTION")):
            if not cid.isdigit() or int(cid) not in keep:
                continue
            institution = inst or other
            mp = matcher.match(first, last, title, institution)
            matched += mp is not None
            display = person(HONORIFICS.sub(" ", first), re.sub(r",.*$", "", HONORIFICS.sub(" ", last)))
            off_w.add((int(cid), display, re.sub(r"\s+", " ", title).strip(), institution.strip(), branch, mp))
        off_w.flush()
        stats["officials"], stats["mp_links"] = off_w.count, matched
        say("Reading subjects", 2, 4)

        subj_w = _Writer(conn, "INSERT INTO comm_subject VALUES (?,?,?)")
        for (cid, code, custom) in read_rows(cz, "Communication_SubjectMattersExport.csv",
                                             ("COMLOG_ID", "SUBJECT_CODE_OBJET"), ("CUSTOM_SUBJ_OBJET_PERSO",)):
            if cid.isdigit() and int(cid) in keep:
                subj_w.add((int(cid), code, custom))
        subj_w.flush()
        say("Reading descriptions", 3, 4)

        mentions = []
        finder = MentionFinder()
        det_w = _Writer(conn, "INSERT INTO comm_detail VALUES (?,?,?)")
        try:
            for (cid, codes, desc) in read_rows(cz, "Communication_SubjectMatterDetailsExport.csv",
                                                ("COMLOG_ID", "SUBJECT_CODE_OBJET", "DESCRIPTION")):
                if not cid.isdigit() or int(cid) not in keep:
                    continue
                cid_i = int(cid)
                desc = desc.replace("\r\n", "\n").strip()
                det_w.add((cid_i, codes, desc))
                client, cdate = keep[cid_i]
                for number, window, snippet, kind in finder(desc):
                    mentions.append({"source": "comm", "ref": cid_i, "client": client, "number": number,
                                     "window": window, "when": _ymd(cdate), "kind": kind, "snippet": snippet})
        except SchemaError:
            pass  # older exports had no descriptions
        det_w.flush()
        stats["descriptions"] = det_w.count

        # ---- Registrations ----
        say("Reading registrations")
        reg_w = _Writer(conn, "INSERT INTO reg VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)")
        regs: dict[int, tuple] = {}          # id -> (client_num, effective, active)
        active_profiles: dict[int, int] = {}  # profile id -> reg id (in-house)
        consultant_keys: dict[tuple, int] = {}  # (registrant, profile) -> reg id
        for row in read_rows(
                rz, "Registration_PrimaryExport.csv",
                ("REG_ID_ENR", "REG_TYPE_ENR", "REG_NUM_ENR", "EN_FIRM_NM_FIRME_AN", "FR_FIRM_NM_FIRME",
                 "RGSTRNT_NUM_DECLARANT", "RGSTRNT_LAST_NM_DCLRNT", "RGSTRNT_1ST_NM_PRENOM_DCLRNT",
                 "RO_POS_POSTE_AR", "RGSTRNT_POS_POSTE_DCLRNT",
                 ("CLIENT_ORG_CORP_PROFIL_ID_PROFIL_CLIENT_ORG_CORP", "CLIENT_ORG_CORP_PROFIL_ID"),
                 "CLIENT_ORG_CORP_NUM", "EN_CLIENT_ORG_CORP_NM_AN", "FR_CLIENT_ORG_CORP_NM",
                 "EFFECTIVE_DATE_VIGUEUR", "END_DATE_FIN", "POSTED_DATE_PUBLICATION"),
                ("GOVT_FUND_IND_FIN_GOUV", "CONTG_FEE_IND_HON_COND", "PARENT_IND_SOC_MERE",
                 "COALITION_IND", "SUBSIDIARY_IND_FILIALE")):
            (rid, rtype, rnum, firm_en, firm_fr, regnum, rlast, rfirst, ro_pos, rg_pos, profile, cnum,
             cen, cfr, eff, end, posted, funding, contingency, parent, coalition, subsidiary) = row
            eff, end = iso_date(eff), iso_date(end)
            if not rid.isdigit() or (end and end < since_s):
                continue
            active = 1 if not end or end >= today.isoformat() else 0
            rid_i, rtype_i, profile_i, regnum_i = int(rid), to_int(rtype), to_int(profile), to_int(regnum)
            regs[rid_i] = (to_int(cnum), eff, active)
            if active and profile_i:
                if rtype_i in (2, 3):
                    active_profiles[profile_i] = rid_i
                elif rtype_i == 1 and regnum_i:
                    consultant_keys[(regnum_i, profile_i)] = rid_i
            reg_w.add((rid_i, rtype_i, rnum, org_name(firm_en, firm_fr), regnum_i, person(rfirst, rlast),
                       ro_pos or rg_pos, profile_i, to_int(cnum), org_name(cen, cfr), eff, end, iso_date(posted),
                       active, funding, contingency, parent, coalition, subsidiary))
        reg_w.flush()
        active_ids = {rid for rid, v in regs.items() if v[2]}
        stats["registrations"], stats["active_registrations"] = len(regs), len(active_ids)
        say("Reading what registrations cover", 1, 5)

        rdet_w = _Writer(conn, "INSERT INTO reg_detail VALUES (?,?,?,?)")
        reg_mentions = []
        for (rid, desc, cats, codes) in read_rows(
                rz, "Registration_SubjectMatterDetailsExport.csv",
                ("REG_ID_ENR", "DESCRIPTION"), ("ASSOC_CAT_CODES", "ASSOC_SUBJECT_CODES_OBJET")):
            if not rid.isdigit() or int(rid) not in regs:
                continue
            rid_i = int(rid)
            desc = desc.replace("\r\n", "\n").strip()
            if rid_i in active_ids:
                rdet_w.add((rid_i, cats, codes, desc))
            client, eff, active = regs[rid_i]
            for number, window, snippet, kind in finder(desc):
                reg_mentions.append({"source": "reg", "ref": rid_i, "client": client, "number": number,
                                     "window": window, "when": _ymd(eff), "kind": kind, "snippet": snippet})
        rdet_w.flush()
        finder = None
        say("Reading subject areas", 2, 5)

        rs_w = _Writer(conn, "INSERT INTO reg_subject VALUES (?,?,?)")
        for (rid, code, custom) in read_rows(rz, "Registration_SubjectMattersExport.csv",
                                             ("REG_ID_ENR", "SUBJECT_CODE_OBJET"), ("CUSTOM_SUBJ_OBJET_PERSO",)):
            if rid.isdigit() and int(rid) in active_ids:
                rs_w.add((int(rid), code, custom))
        rs_w.flush()

        ri_w = _Writer(conn, "INSERT INTO reg_institution VALUES (?,?)")
        for (rid, inst) in read_rows(rz, "Registration_GovernmentInstExport.csv", ("REG_ID_ENR", "INSTITUTION")):
            if rid.isdigit() and int(rid) in active_ids and inst:
                ri_w.add((int(rid), inst.strip()))
        try:
            for (rid, inst) in read_rows(rz, "Registration_ManuallyEntered_GovernmentInstExport.csv",
                                         ("REG_ID_ENR", "OTHER_INSTITUTION_AUTRE")):
                if rid.isdigit() and int(rid) in active_ids and inst:
                    ri_w.add((int(rid), inst.strip()))
        except SchemaError:
            pass
        ri_w.flush()
        say("Reading lobbyists", 3, 5)

        lob_w = _Writer(conn, "INSERT INTO lobbyist VALUES (?,?,?,?,?,?,?)")
        lobbyist_ids = set()
        for (profile, lid, pos, last, first, dpoh, poh) in read_rows(
                rz, "Registration_InHouseLobbyistsExport.csv",
                (("CLIENT_ORG_CORP_PROFIL_ID_PROFIL_CLIENT_ORG_CORP", "CLIENT_ORG_CORP_PROFIL_ID"),
                 "LBBYST_ID_LBBYST", "LBBYST_POSITION_POSTE_LBBYST", "LBBYST_LAST_NM_LBBYST",
                 ("LBBYST_FIRST_NM_PRENOM_LBBYST", "LBBYST_1ST_NM_PRENOM_LBBYST")),
                ("DPOH_IND_TCPD", "POH_IND_TCP")):
            rid = active_profiles.get(to_int(profile) or -1)
            if rid is None:
                continue
            lob_w.add((rid, to_int(lid), person(first, last), pos, int(dpoh == "Y"), int(poh == "Y"), "in-house"))
            if to_int(lid):
                lobbyist_ids.add(to_int(lid))
        for (regnum, profile, lid, last, first, dpoh, poh) in read_rows(
                rz, "Registration_ConsultantLobbyistsExport.csv",
                ("RGSTRNT_NUM_DECLARANT",
                 ("CLIENT_ORG_CORP_PROFIL_ID_PROFIL_CLIENT_ORG_CORP", "CLIENT_ORG_CORP_PROFIL_ID"),
                 "LBBYST_ID_LBBYST", "LBBYST_LAST_NM_LBBYST",
                 ("LBBYST_1ST_NM_PRENOM_LBBYST", "LBBYST_FIRST_NM_PRENOM_LBBYST")),
                ("DPOH_IND_TCPD", "POH_IND_TCP")):
            rid = consultant_keys.get((to_int(regnum) or -1, to_int(profile) or -1))
            if rid is None:
                continue
            lob_w.add((rid, to_int(lid), person(first, last), "", int(dpoh == "Y"), int(poh == "Y"), "consultant"))
            if to_int(lid):
                lobbyist_ids.add(to_int(lid))
        lob_w.flush()
        say("Reading former public offices", 4, 5)

        po_w = _Writer(conn, "INSERT INTO public_office VALUES (?,?,?,?,?,?,?,?)")
        try:
            for (lid, dpoh, title, branch, inst, start, end, details) in read_rows(
                    rz, "Registration_PublicOfficeExport.csv",
                    ("LOBBYIST_ID_LOBBYISTE",), ("DPOH_IND_TCPD", "TITLE_TITRE", "BRANCH_DIRECTION", "INSTITUTION",
                                                 "POS_START_DATE_DEBUT_POSTE", "POS_END_DATE_FIN_POSTE",
                                                 "POH_DETAILS_PRE_V5_INFO_TCP")):
                lid_i = to_int(lid)
                if lid_i in lobbyist_ids and (title or inst or details):
                    po_w.add((lid_i, title, branch, inst, iso_date(start), iso_date(end), int(dpoh == "Y"),
                              details[:600]))
        except SchemaError:
            pass
        po_w.flush()

    # ---- Bills named in descriptions ----
    say("Linking bills")
    resolved = resolve_all(mentions + reg_mentions, resolver)
    seen = set()
    bm_w = _Writer(conn, "INSERT INTO bill_mention VALUES (?,?,?,?,?,?,?,?)")
    for it in sorted(resolved, key=lambda m: (m["when"] or date.min), reverse=True):
        key = (it["source"], it["ref"], it["session"], it["number"])
        if key in seen:
            continue
        seen.add(key)
        bm_w.add((it["source"], it["ref"], it["client"], it["session"], it["number"],
                  it["when"].isoformat() if it["when"] else "", it["snippet"], it["how"]))
    bm_w.flush()
    stats["bill_mentions"] = bm_w.count
    stats["bill_mentions_found"] = len(mentions) + len(reg_mentions)
    stats["bills_complete"] = int(resolver.complete)

    # ---- Summary tables ----
    say("Summarizing")
    conn.executescript(INDEXES)
    conn.execute("""
        INSERT INTO org (num, name, fold, kind, reports, reports_now, mp_reports, first_date, last_date, active_regs)
        SELECT num, '', '', NULL, 0, 0, 0, NULL, NULL, 0 FROM (
            SELECT client_num AS num FROM comm WHERE client_num IS NOT NULL
            UNION SELECT client_num FROM reg WHERE client_num IS NOT NULL)""")
    conn.execute("""
        UPDATE org SET
          reports = (SELECT COUNT(*) FROM comm WHERE comm.client_num = org.num),
          reports_now = (SELECT COUNT(*) FROM comm WHERE comm.client_num = org.num AND comm_date >= ?),
          first_date = (SELECT MIN(comm_date) FROM comm WHERE comm.client_num = org.num),
          last_date = (SELECT MAX(comm_date) FROM comm WHERE comm.client_num = org.num),
          active_regs = (SELECT COUNT(*) FROM reg WHERE reg.client_num = org.num AND active = 1),
          mp_reports = (SELECT COUNT(DISTINCT c.id) FROM comm c JOIN comm_official o ON o.comm_id = c.id
                        WHERE c.client_num = org.num AND o.mp_id IS NOT NULL AND c.comm_date >= ?)""",
                 (now_s, now_s))
    # Latest name and kind: from the newest registration, else the newest report.
    names = {}
    for num, name, rtype, when in conn.execute(
            "SELECT client_num, client, reg_type, effective FROM reg WHERE client <> '' ORDER BY effective"):
        names[num] = (name, rtype, when or "")
    for num, name, rtype, when in conn.execute(
            "SELECT client_num, client, reg_type, comm_date FROM comm WHERE client <> '' ORDER BY comm_date"):
        if num not in names or when > names[num][2]:
            names[num] = (name, names.get(num, (None, rtype))[1] or rtype, when)
    kinds = {}
    for num, rtype in conn.execute("SELECT client_num, MAX(reg_type) FROM reg GROUP BY client_num"):
        kinds[num] = rtype
    conn.executemany("UPDATE org SET name = ?, fold = ?, kind = ? WHERE num = ?",
                     [(n, fold(n), kinds.get(num) or rt, num) for num, (n, rt, _) in names.items()])
    conn.execute("DELETE FROM org WHERE name = ''")

    conn.execute("""
        INSERT INTO registrant (num, name, fold, firm, kind, position, reports, reports_now, last_date, active_regs)
        SELECT num, '', '', '', NULL, '', 0, 0, NULL, 0 FROM (
            SELECT registrant_num AS num FROM comm WHERE registrant_num IS NOT NULL
            UNION SELECT registrant_num FROM reg WHERE registrant_num IS NOT NULL)""")
    conn.execute("""
        UPDATE registrant SET
          reports = (SELECT COUNT(*) FROM comm WHERE comm.registrant_num = registrant.num),
          reports_now = (SELECT COUNT(*) FROM comm WHERE comm.registrant_num = registrant.num AND comm_date >= ?),
          last_date = (SELECT MAX(comm_date) FROM comm WHERE comm.registrant_num = registrant.num),
          active_regs = (SELECT COUNT(*) FROM reg WHERE reg.registrant_num = registrant.num AND active = 1)""",
                 (now_s,))
    info = {}
    for num, name, firm, rtype, pos, when in conn.execute(
            "SELECT registrant_num, registrant, firm, reg_type, position, effective FROM reg ORDER BY effective"):
        info[num] = (name, firm, rtype, pos, when or "")
    for num, name, rtype, when in conn.execute(
            "SELECT registrant_num, registrant, reg_type, comm_date FROM comm ORDER BY comm_date"):
        old = info.get(num)
        if old is None:
            info[num] = (name, "", rtype, "", when)
        elif when > old[4] and name:
            info[num] = (name, old[1], old[2], old[3], when)
    conn.executemany("UPDATE registrant SET name = ?, fold = ?, firm = ?, kind = ?, position = ? WHERE num = ?",
                     [(n, fold(n), f or "", k, p or "", num) for num, (n, f, k, p, _) in info.items() if n])
    conn.execute("DELETE FROM registrant WHERE name = ''")
    # A consultant is usually listed as a lobbyist on their own registrations: that gives the ID
    # under which their former public offices are filed.
    links = {}
    for num, name, lid in conn.execute("""
            SELECT r.registrant_num, l.name, l.lobbyist_id FROM lobbyist l JOIN reg r ON r.id = l.reg_id
            WHERE l.lobbyist_id IS NOT NULL"""):
        links.setdefault((num, fold(name)), lid)
    conn.executemany("UPDATE registrant SET lobbyist_id = ? WHERE num = ?",
                     [(links[(num, f)], num) for num, f in conn.execute("SELECT num, fold FROM registrant")
                      if (num, f) in links])

    stats.update(organizations=conn.execute("SELECT COUNT(*) FROM org").fetchone()[0],
                 registrants=conn.execute("SELECT COUNT(*) FROM registrant").fetchone()[0],
                 seconds=round(time.time() - started, 1))
    meta_rows = {"schema": SCHEMA_VERSION, "built": datetime.now().isoformat(timespec="seconds"),
                 "since": since_s, "today": today.isoformat(), "mps_known": str(len(members or [])),
                 **{k: str(v) for k, v in stats.items()}, **{k: str(v) for k, v in (meta or {}).items()}}
    conn.executemany("INSERT OR REPLACE INTO meta VALUES (?, ?)", meta_rows.items())
    conn.commit()
    conn.execute("ANALYZE")
    conn.close()
    os.replace(tmp, out_path)
    return stats


# --------------------------------------------------------------------------
# Reading the database (used by the pages)
# --------------------------------------------------------------------------
class Connection(sqlite3.Connection):
    """A read-only connection that can also carry the database's meta table."""
    meta: dict = {}


def connect(path: str | None = None) -> Connection | None:
    path = path or DB_PATH
    if not os.path.exists(path):
        return None
    conn = sqlite3.connect(f"file:{path}?mode=ro", uri=True, check_same_thread=False, factory=Connection)
    conn.row_factory = sqlite3.Row
    return conn


def read_meta(path: str | None = None) -> dict:
    conn = connect(path)
    if conn is None:
        return {}
    try:
        return dict(conn.execute("SELECT key, value FROM meta"))
    except sqlite3.DatabaseError:
        return {}
    finally:
        conn.close()


PAGE_SIZE = 25


def _in(ids) -> str:
    return ",".join("?" * len(ids))


def subject_names(conn) -> dict[str, str]:
    return dict(conn.execute("SELECT code, name FROM subject"))


def enrich_reports(conn, rows) -> list[dict]:
    """Attach officials, subjects and descriptions to communication report rows."""
    reports = [dict(r) for r in rows]
    if not reports:
        return []
    ids = [r["id"] for r in reports]
    officials, subjects, details = defaultdict(list), defaultdict(list), defaultdict(list)
    for r in conn.execute(f"SELECT * FROM comm_official WHERE comm_id IN ({_in(ids)}) ORDER BY mp_id IS NULL, rowid", ids):
        officials[r["comm_id"]].append(dict(r))
    names = subject_names(conn)
    for r in conn.execute(f"SELECT * FROM comm_subject WHERE comm_id IN ({_in(ids)})", ids):
        label = r["custom"] if r["code"] == "SMT-12" and r["custom"] else names.get(r["code"], r["code"])
        if label not in subjects[r["comm_id"]]:
            subjects[r["comm_id"]].append(label)
    for r in conn.execute(f"SELECT * FROM comm_detail WHERE comm_id IN ({_in(ids)})", ids):
        if r["description"] and r["description"] not in details[r["comm_id"]]:
            details[r["comm_id"]].append(r["description"])
    bills = defaultdict(list)
    for r in conn.execute(f"SELECT ref_id, session, number FROM bill_mention WHERE source = 'comm' AND ref_id IN ({_in(ids)})", ids):
        if (r["session"], r["number"]) not in bills[r["ref_id"]]:
            bills[r["ref_id"]].append((r["session"], r["number"]))
    for rep in reports:
        rep["officials"] = officials[rep["id"]]
        rep["subjects"] = sorted(subjects[rep["id"]])
        rep["details"] = details[rep["id"]]
        rep["bills"] = sorted(bills[rep["id"]], key=lambda b: (b[0] != CURRENT[0], b[1]))
        rep["url"] = REPORT_URL.format(id=rep["id"])
        rep["date"] = _ymd(rep["comm_date"])
        rep["kind"] = REG_TYPES.get(rep["reg_type"], "")
    return reports


def overview(conn, today: date | None = None) -> dict:
    """Totals and leaderboards for the lobbying home page."""
    today = today or date.today()
    now_s = CURRENT[1].isoformat()
    recent_s = (today - timedelta(days=90)).isoformat()
    one = lambda sql, *a: conn.execute(sql, a).fetchone()[0]
    totals = {
        "reports": one("SELECT COUNT(*) FROM comm WHERE comm_date >= ?", now_s),
        "orgs": one("SELECT COUNT(DISTINCT client_num) FROM comm WHERE comm_date >= ?", now_s),
        "mp_reports": one("""SELECT COUNT(DISTINCT c.id) FROM comm c JOIN comm_official o ON o.comm_id = c.id
                             WHERE c.comm_date >= ? AND o.mp_id IS NOT NULL""", now_s),
        "active_regs": one("SELECT COUNT(*) FROM reg WHERE active = 1"),
        "latest": one("SELECT MAX(comm_date) FROM comm"),
    }
    top_orgs = [dict(r) for r in conn.execute("""
        SELECT c.client_num AS num, o.name, COUNT(*) AS n FROM comm c JOIN org o ON o.num = c.client_num
        WHERE c.comm_date >= ? GROUP BY c.client_num ORDER BY n DESC, o.name LIMIT 10""", (recent_s,))]
    top_inst = [dict(r) for r in conn.execute("""
        SELECT o.institution AS name, COUNT(DISTINCT o.comm_id) AS n FROM comm_official o JOIN comm c ON c.id = o.comm_id
        WHERE c.comm_date >= ? AND o.institution <> '' GROUP BY o.institution ORDER BY n DESC LIMIT 10""", (recent_s,))]
    top_mps = [dict(r) for r in conn.execute("""
        SELECT o.mp_id AS id, COUNT(DISTINCT o.comm_id) AS n FROM comm_official o JOIN comm c ON c.id = o.comm_id
        WHERE c.comm_date >= ? AND o.mp_id IS NOT NULL GROUP BY o.mp_id ORDER BY n DESC LIMIT 10""", (recent_s,))]
    top_subjects = [dict(r) for r in conn.execute("""
        SELECT s.code, COALESCE(n.name, s.code) AS name, COUNT(DISTINCT s.comm_id) AS n
        FROM comm_subject s JOIN comm c ON c.id = s.comm_id LEFT JOIN subject n ON n.code = s.code
        WHERE c.comm_date >= ? AND s.code <> 'SMT-12' GROUP BY s.code ORDER BY n DESC LIMIT 10""", (recent_s,))]
    top_bills = [dict(r) for r in conn.execute("""
        SELECT session, number, COUNT(DISTINCT client_num) AS orgs, COUNT(*) AS n FROM bill_mention
        WHERE source = 'comm' AND session = ? AND mention_date >= ?
        GROUP BY session, number ORDER BY orgs DESC, n DESC LIMIT 10""", (CURRENT[0], recent_s))]
    for group in (top_orgs, top_inst, top_mps, top_subjects, top_bills):
        peak = max((g.get("orgs", g["n"]) for g in group), default=0) or 1
        for g in group:
            g["width"] = round(g.get("orgs", g["n"]) / peak * 100, 1)
    return {"totals": totals, "top_orgs": top_orgs, "top_institutions": top_inst, "top_mps": top_mps,
            "top_subjects": top_subjects, "top_bills": top_bills, "recent_from": _ymd(recent_s)}


def latest_reports(conn, subject: str = "", mps_only: bool = False, limit: int = PAGE_SIZE, offset: int = 0):
    where, args = ["1=1"], []
    if subject:
        where.append("c.id IN (SELECT comm_id FROM comm_subject WHERE code = ?)")
        args.append(subject)
    if mps_only:
        where.append("c.id IN (SELECT comm_id FROM comm_official WHERE mp_id IS NOT NULL)")
    rows = conn.execute(f"""SELECT c.* FROM comm c WHERE {' AND '.join(where)}
                            ORDER BY c.comm_date DESC, c.id DESC LIMIT ? OFFSET ?""", (*args, limit + 1, offset)).fetchall()
    return enrich_reports(conn, rows[:limit]), len(rows) > limit


def org_profile(conn, num: int) -> dict | None:
    org = conn.execute("SELECT * FROM org WHERE num = ?", (num,)).fetchone()
    if org is None:
        return None
    org = dict(org)
    org["kind_label"] = ORG_KINDS.get(org["kind"], "")
    names = subject_names(conn)
    regs = []
    for r in conn.execute("SELECT * FROM reg WHERE client_num = ? AND active = 1 ORDER BY reg_type DESC, effective DESC", (num,)):
        reg = dict(r)
        reg["type_label"] = REG_TYPES.get(reg["reg_type"], "")
        reg["url"] = REGISTRY_SEARCH_URL
        reg["subjects"] = sorted({(x["custom"] if x["code"] == "SMT-12" and x["custom"] else names.get(x["code"], x["code"]))
                                  for x in conn.execute("SELECT * FROM reg_subject WHERE reg_id = ?", (reg["id"],))})
        reg["institutions"] = sorted({x[0] for x in conn.execute("SELECT institution FROM reg_institution WHERE reg_id = ?", (reg["id"],))})
        reg["details"] = [dict(x) for x in conn.execute("SELECT * FROM reg_detail WHERE reg_id = ? ORDER BY rowid", (reg["id"],))]
        reg["lobbyists"] = _lobbyists(conn, reg["id"])
        regs.append(reg)
    org["registrations"] = regs
    org["bills"] = [dict(r) for r in conn.execute("""
        SELECT session, number, COUNT(*) AS n, MAX(mention_date) AS last, MAX(CASE WHEN source = 'reg' THEN 1 ELSE 0 END) AS registered,
               (SELECT snippet FROM bill_mention m2 WHERE m2.client_num = m.client_num AND m2.session = m.session
                AND m2.number = m.number ORDER BY mention_date DESC LIMIT 1) AS snippet
        FROM bill_mention m WHERE client_num = ? GROUP BY session, number
        ORDER BY session = ? DESC, last DESC""", (num, CURRENT[0]))]
    org["monthly"] = monthly_counts(conn, "client_num", num)
    org["top_mps"] = [dict(r) for r in conn.execute("""
        SELECT o.mp_id AS id, COUNT(DISTINCT c.id) AS n, MAX(c.comm_date) AS last FROM comm c
        JOIN comm_official o ON o.comm_id = c.id WHERE c.client_num = ? AND o.mp_id IS NOT NULL AND c.comm_date >= ?
        GROUP BY o.mp_id ORDER BY n DESC LIMIT 12""", (num, CURRENT[1].isoformat()))]
    org["top_institutions"] = [dict(r) for r in conn.execute("""
        SELECT o.institution AS name, COUNT(DISTINCT c.id) AS n FROM comm c JOIN comm_official o ON o.comm_id = c.id
        WHERE c.client_num = ? AND c.comm_date >= ? AND o.institution <> '' GROUP BY o.institution ORDER BY n DESC LIMIT 8""",
        (num, CURRENT[1].isoformat()))]
    org["registrants"] = [dict(r) for r in conn.execute("""
        SELECT c.registrant_num AS num, MAX(c.registrant) AS name, COUNT(*) AS n FROM comm c
        WHERE c.client_num = ? GROUP BY c.registrant_num ORDER BY n DESC LIMIT 10""", (num,))]
    return org


def _lobbyists(conn, reg_id: int) -> list[dict]:
    people = [dict(r) for r in conn.execute("SELECT * FROM lobbyist WHERE reg_id = ? ORDER BY former_dpoh DESC, name", (reg_id,))]
    ids = [p["lobbyist_id"] for p in people if p["lobbyist_id"]]
    offices = defaultdict(list)
    if ids:
        for r in conn.execute(f"SELECT * FROM public_office WHERE lobbyist_id IN ({_in(ids)}) ORDER BY end_date DESC", ids):
            offices[r["lobbyist_id"]].append(dict(r))
    for p in people:
        p["offices"] = offices.get(p["lobbyist_id"], [])[:4]
    return people


def monthly_counts(conn, column: str, value, months: int = 24, today: date | None = None) -> list[dict]:
    today = today or date.today()
    start = date(today.year, today.month, 1)
    for _ in range(months - 1):
        start = (start - timedelta(days=1)).replace(day=1)
    assert column in ("client_num", "registrant_num")
    counts = dict(conn.execute(f"""SELECT substr(comm_date, 1, 7), COUNT(*) FROM comm
                                   WHERE {column} = ? AND comm_date >= ? GROUP BY 1""", (value, start.isoformat())))
    out, d = [], start
    for _ in range(months):
        key = d.strftime("%Y-%m")
        out.append({"month": d, "n": counts.get(key, 0)})
        d = (d + timedelta(days=32)).replace(day=1)
    peak = max((m["n"] for m in out), default=0) or 1
    for m in out:
        m["height"] = round(m["n"] / peak * 100, 1)
    return out


def reports_for(conn, column: str, value, limit: int = PAGE_SIZE, offset: int = 0):
    assert column in ("client_num", "registrant_num")
    rows = conn.execute(f"SELECT * FROM comm WHERE {column} = ? ORDER BY comm_date DESC, id DESC LIMIT ? OFFSET ?",
                        (value, limit + 1, offset)).fetchall()
    return enrich_reports(conn, rows[:limit]), len(rows) > limit


def registrant_profile(conn, num: int) -> dict | None:
    r = conn.execute("SELECT * FROM registrant WHERE num = ?", (num,)).fetchone()
    if r is None:
        return None
    r = dict(r)
    r["kind_label"] = REG_TYPES.get(r["kind"], "")
    r["clients"] = [dict(x) for x in conn.execute("""
        SELECT g.client_num AS num, MAX(g.client) AS name, MAX(g.firm) AS firm, MAX(g.effective) AS since,
               (SELECT COUNT(*) FROM comm c WHERE c.registrant_num = g.registrant_num AND c.client_num = g.client_num) AS reports
        FROM reg g WHERE g.registrant_num = ? AND g.active = 1 GROUP BY g.client_num ORDER BY name""", (num,))]
    r["past_clients"] = [dict(x) for x in conn.execute("""
        SELECT c.client_num AS num, MAX(c.client) AS name, COUNT(*) AS reports, MAX(c.comm_date) AS last FROM comm c
        WHERE c.registrant_num = ? AND c.client_num NOT IN (SELECT client_num FROM reg WHERE registrant_num = ? AND active = 1)
        GROUP BY c.client_num ORDER BY last DESC LIMIT 30""", (num, num))]
    r["offices"] = [dict(x) for x in conn.execute("SELECT * FROM public_office WHERE lobbyist_id = ? ORDER BY end_date DESC",
                                                  (r["lobbyist_id"] or -1,))]
    r["monthly"] = monthly_counts(conn, "registrant_num", num)
    return r


def mp_summary(conn, pid: int, limit: int = 8) -> dict:
    """Reports listing this MP since the current Parliament opened."""
    ids = [r[0] for r in conn.execute("""
        SELECT DISTINCT o.comm_id FROM comm_official o JOIN comm c ON c.id = o.comm_id
        WHERE o.mp_id = ? AND c.comm_date >= ?""", (pid, CURRENT[1].isoformat()))]
    out = {"total": len(ids), "orgs": [], "org_count": 0, "subjects": [], "title": ""}
    if not ids:
        return out
    by_org: dict = {}
    for r in conn.execute(f"SELECT client_num, client, comm_date FROM comm WHERE id IN ({_in(ids)})", ids):
        o = by_org.setdefault(r[0], {"num": r[0], "name": r[1], "n": 0, "last": ""})
        o["n"] += 1
        o["last"] = max(o["last"], r[2])
    out["org_count"] = len(by_org)
    out["orgs"] = sorted(by_org.values(), key=lambda o: (o["n"], o["last"]), reverse=True)[:limit]
    names = subject_names(conn)
    counts = Counter(code for _, code in conn.execute(
        f"SELECT DISTINCT comm_id, code FROM comm_subject WHERE comm_id IN ({_in(ids)}) AND code <> 'SMT-12'", ids))
    out["subjects"] = [{"name": names.get(code, code), "n": n} for code, n in counts.most_common(6)]
    latest = conn.execute(f"""SELECT o.title FROM comm_official o JOIN comm c ON c.id = o.comm_id
                              WHERE o.mp_id = ? AND o.title <> '' AND c.id IN ({_in(ids)})
                              ORDER BY c.comm_date DESC LIMIT 1""", (pid, *ids)).fetchone()
    out["title"] = latest[0] if latest else ""
    return out


def mp_reports(conn, pid: int, limit: int = PAGE_SIZE, offset: int = 0):
    rows = conn.execute("""SELECT DISTINCT c.* FROM comm c JOIN comm_official o ON o.comm_id = c.id
                           WHERE o.mp_id = ? ORDER BY c.comm_date DESC, c.id DESC LIMIT ? OFFSET ?""",
                        (pid, limit + 1, offset)).fetchall()
    return enrich_reports(conn, rows[:limit]), len(rows) > limit


def bill_lobbying(conn, session: str, number: str) -> dict:
    """Organizations that named this bill in reports or registrations."""
    rows = [dict(r) for r in conn.execute("""
        SELECT m.client_num AS num, o.name AS name,
               SUM(CASE WHEN m.source = 'comm' THEN 1 ELSE 0 END) AS reports,
               MAX(CASE WHEN m.source = 'reg' THEN 1 ELSE 0 END) AS registered,
               MAX(CASE WHEN m.source = 'reg' THEN r.active ELSE 0 END) AS registered_now,
               MAX(m.mention_date) AS last
        FROM bill_mention m JOIN org o ON o.num = m.client_num LEFT JOIN reg r ON m.source = 'reg' AND r.id = m.ref_id
        WHERE m.session = ? AND m.number = ? GROUP BY m.client_num
        ORDER BY reports DESC, registered_now DESC, last DESC""", (session, number.upper()))]
    snippets = {}
    for r in conn.execute("""SELECT client_num, snippet FROM bill_mention WHERE session = ? AND number = ?
                             ORDER BY source = 'comm' DESC, mention_date DESC""", (session, number.upper())):
        snippets.setdefault(r["client_num"], r["snippet"])
    for r in rows:
        r["snippet"] = snippets.get(r["num"], "")
    mps = [dict(r) for r in conn.execute("""
        SELECT o.mp_id AS id, COUNT(DISTINCT c.id) AS n FROM bill_mention m JOIN comm c ON m.source = 'comm' AND c.id = m.ref_id
        JOIN comm_official o ON o.comm_id = c.id WHERE m.session = ? AND m.number = ? AND o.mp_id IS NOT NULL
        GROUP BY o.mp_id ORDER BY n DESC LIMIT 10""", (session, number.upper()))]
    reports = conn.execute("SELECT COUNT(*) FROM bill_mention WHERE source = 'comm' AND session = ? AND number = ?",
                           (session, number.upper())).fetchone()[0]
    return {"orgs": rows, "reports": reports, "mps": mps}


def search(conn, words: list[str], limit: int = 25) -> dict:
    """Organizations and lobbyists whose names contain every word (accent-insensitive)."""
    if not words:
        return {"orgs": [], "lobbyists": []}
    cond = " AND ".join("fold LIKE ?" for _ in words)
    args = [f"%{w}%" for w in words]
    orgs = [dict(r) for r in conn.execute(
        f"SELECT * FROM org WHERE {cond} ORDER BY reports_now DESC, reports DESC, active_regs DESC LIMIT ?", (*args, limit))]
    people = [dict(r) for r in conn.execute(
        f"SELECT * FROM registrant WHERE {cond} ORDER BY reports_now DESC, active_regs DESC, reports DESC LIMIT ?", (*args, limit))]
    for o in orgs:
        o["kind_label"] = ORG_KINDS.get(o["kind"], "")
    for p in people:
        p["kind_label"] = REG_TYPES.get(p["kind"], "")
    return {"orgs": orgs, "lobbyists": people}


def subjects_in_use(conn) -> list[dict]:
    return [dict(r) for r in conn.execute("""
        SELECT s.code, s.name FROM subject s WHERE s.code <> 'SMT-12' ORDER BY s.name""")]


# --------------------------------------------------------------------------
# Refreshing, in a separate process
#
# The website starts `python lobbying.py build <job.json>` in the background. Running it as its
# own process keeps the build's memory (and its CPU time) away from the web server: when the
# build ends, everything it used is handed back. Progress goes to a small JSON file the website
# reads for the progress bar.
# --------------------------------------------------------------------------
PROGRESS_PATH = DB_PATH + ".progress.json"

# (label, share of the whole job when the step starts)
BUILD_STEPS = {
    "Downloading registrations": 0.0, "Downloading communication reports": 0.30,
    "Reading communication reports": 0.38, "Reading officials met": 0.45, "Reading subjects": 0.50,
    "Reading descriptions": 0.53, "Reading registrations": 0.57, "Reading what registrations cover": 0.60,
    "Reading subject areas": 0.70, "Reading lobbyists": 0.80, "Reading former public offices": 0.84,
    "Linking bills": 0.86, "Summarizing": 0.90,
}


def write_progress(path: str, **state) -> None:
    import json
    state["time"] = time.time()
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f)
    os.replace(tmp, path)


def read_progress(path: str = PROGRESS_PATH) -> dict:
    import json
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def run_job(job: dict) -> dict:
    """Download both ZIPs and build the database. job: db, progress, members, bills, and
    optionally reg_url, comm_url, reg_modified, comm_modified."""
    progress_path = job.get("progress") or PROGRESS_PATH
    state = {"status": "running", "label": "Starting", "pct": 0.0, "error": None}

    def say(label, done=0, total=0):
        start = BUILD_STEPS.get(label)
        if start is not None:
            state["label"], state["pct"] = label, start
        if total and state["label"] in BUILD_STEPS:
            keys = list(BUILD_STEPS)
            i = keys.index(state["label"])
            end = BUILD_STEPS[keys[i + 1]] if i + 1 < len(keys) else 1.0
            state["pct"] = BUILD_STEPS[state["label"]] + (end - BUILD_STEPS[state["label"]]) * min(done / total, 1)
        write_progress(progress_path, **state)

    bills = []
    for b in job.get("bills") or []:
        b = dict(b)
        b["introduced"] = _ymd(b.get("introduced") or "")
        bills.append(b)
    workdir = tempfile.mkdtemp(prefix="politikit-lobbying-")
    reg_zip, comm_zip = os.path.join(workdir, "registrations.zip"), os.path.join(workdir, "communications.zip")
    try:
        last = [0.0]

        def bytes_progress(label):
            def cb(got, total):
                if time.time() - last[0] > 1:
                    last[0] = time.time()
                    say(label, got, total or 90_000_000)
            return cb

        say("Downloading registrations")
        reg = download(job.get("reg_url") or REGISTRATIONS_URL, reg_zip, bytes_progress("Downloading registrations"), "registrations")
        say("Downloading communication reports")
        comm = download(job.get("comm_url") or COMMUNICATIONS_URL, comm_zip, bytes_progress("Downloading communication reports"), "communications")
        stats = build_database(reg_zip, comm_zip, job["db"], job.get("members") or [], bills, progress=say,
                               meta={"reg_modified": reg["modified"], "comm_modified": comm["modified"],
                                     "reg_url": reg["url"], "comm_url": comm["url"]})
        state.update(status="done", label="Done", pct=1.0, stats=stats)
        write_progress(progress_path, **state)
        return stats
    except Exception as exc:  # report every failure to the website instead of dying silently
        state.update(status="error", error=f"{type(exc).__name__}: {exc}")
        write_progress(progress_path, **state)
        raise
    finally:
        for p in (reg_zip, comm_zip):
            try:
                os.remove(p)
            except OSError:
                pass
        try:
            os.rmdir(workdir)
        except OSError:
            pass


if __name__ == "__main__":
    import json
    import sys
    if len(sys.argv) == 3 and sys.argv[1] == "build":
        with open(sys.argv[2], encoding="utf-8") as f:
            job = json.load(f)
        try:
            print(json.dumps(run_job(job)))
        except Exception as exc:
            print(f"Lobbying build failed: {exc}", file=sys.stderr)
            sys.exit(1)
    else:
        print("usage: python lobbying.py build job.json", file=sys.stderr)
        sys.exit(2)
