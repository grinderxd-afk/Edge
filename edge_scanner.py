#!/usr/bin/env python3
"""
Edge scanner
============
Builds a phone-friendly HTML page (index.html) with, for every selection:

  * true probability  = the sharp book's odds with its margin (vig) removed
  * fair odds         = 1 / true probability
  * min odds          = (1 + your minimum edge) / true probability   (done in the page)
  * Bet365 odds/edge  = optional: set compare_book to "bet365" in config.json (costs extra requests)

The page recalculates min odds, edge and stake in the browser when you change
the settings, so changing them never uses API requests.

Uses the OddsPapi v4 API (the one free account keys work with).

Usage
-----
    python edge_scanner.py                    # sample data (made up), writes index.html
    python edge_scanner.py --test             # checks the math and the live-data parsing

  One-time setup for live data:
    python edge_scanner.py --check            # does your key work? what's on your plan? (free)
    python edge_scanner.py --find-tournaments --sport Soccer --search "uefa,champions,europa"
                                              # find tournament IDs, then put them in config.json
    python edge_scanner.py --find-markets "corner,both teams"   # 1 request: see how a market is named
    python edge_scanner.py --build-markets    # 1 request: saves market definitions
    python edge_scanner.py --build-participants   # 1 request per sport: saves team names

  Every day:
    python edge_scanner.py --live             # 1 request per sport (2 if Bet365 is on), writes index.html
    python edge_scanner.py --live --lock      # same, but password-protected (set PAGE_PASSWORD first)

Your API key is read from the ODDSPAPI_KEY environment variable, or from a
file named .env next to this script (ODDSPAPI_KEY=...), or you're asked for it.
It is never written into index.html and never printed.
"""

import argparse
import base64
import getpass
import hashlib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from datetime import datetime, timedelta, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CONFIG_PATH = HERE / "config.json"
MARKETS_CACHE_PATH = HERE / "markets_cache.json"
PARTICIPANTS_CACHE_PATH = HERE / "participants_cache.json"

SPORTS = ["Soccer", "Football", "Baseball", "Basketball", "Hockey"]
# OddsPapi sport IDs. "Football" here means American football, "Hockey" means ice hockey.
SPORT_IDS = {"Soccer": 10, "Basketball": 11, "Baseball": 13, "Football": 14, "Hockey": 15}
SHARP_BOOK = "Pinnacle"

DEVIG_LABELS = {
    "power": "power method",
    "proportional": "proportional method",
}

DEFAULT_CONFIG = {
    "sharp_book": "pinnacle",          # bookmaker slug used as the "true probability" benchmark
    "sharp_label": "Pinnacle",         # name shown on the page
    "compare_book": None,             # set to "bet365" to also fetch it (one extra request per sport; needs it on your plan)
    "base_url": "https://api.oddspapi.io",   # OddsPapi v4
    "max_requests_per_run": 10,        # a safety stop so one run can't burn your quota
    "request_gap_seconds": 1.1,        # OddsPapi asks for 1 second between calls
    "market_types": ["moneyline", "1x2", "totals", "spreads", "btts", "corners_totals"],
    "combine_sports": False,           # True = pack leagues from all sports together, 5 per request (saves quota)
    "periods": ["result", "fulltime"],  # full game only (no halves or quarters)
    "min_minutes_to_start": 10,
    "sharp_extra_books": [],           # more sharp books to average with the main one, e.g. ["singbet"] (1 extra request per group each)
    "sharp_weights": {},               # optional weight per book slug; the main sharp book counts 2 and each extra book 1 by default
    "compare_label": None,             # name shown for the comparison book, e.g. "Betano MX"
    "your_book_label": "your book",    # the book you actually bet at, e.g. "Playdoit"
    "compare_factor": 1.0,             # estimated price at your book = comparison book's price x this (from --compare-books)
    "compare_spread_pct": 0.0,         # how far apart the two books' prices typically are, in % (from --compare-books)
    "compare_sports": None,            # (older setting) sports the factor above applies to; None = all sports
    "compare_by_sport": {},            # per sport, measured with --compare-books: {"Soccer": {"factor": 1.0, "spread_pct": 3.0}}
    "compare_default": None,           # used for sports not listed above, e.g. {"factor": 1.0, "spread_pct": 5.0}; None = no estimate
    "calibration_books": ["betano.mx", "betcris", "winpot.mx", "codere.es", "rushbet.co", "bet365"],
    "tournaments": {                    # IDs confirmed with --find-tournaments
        "Soccer": [
            {"id": 17, "name": "Premier League (England)"},
            {"id": 8, "name": "LaLiga (Spain)"},
            {"id": 7, "name": "UEFA Champions League"},
            {"id": 679, "name": "UEFA Europa League"},
            {"id": 34480, "name": "UEFA Conference League"},
        ],
        "Football": [{"id": 31, "name": "NFL"}],
        "Baseball": [{"id": 109, "name": "MLB"}],
        "Basketball": [{"id": 132, "name": "NBA"}],
        "Hockey": [{"id": 234, "name": "NHL"}],
    },
}


# --------------------------------------------------------------------------
# Math
# --------------------------------------------------------------------------
def _check_odds(odds):
    if len(odds) < 2:
        raise ValueError("A market needs at least two outcomes.")
    if any(o is None or o <= 1.0 for o in odds):
        raise ValueError(f"Decimal odds must be greater than 1.0, got {odds}")


def devig_proportional(odds):
    """Divide each implied probability by the total (the overround)."""
    _check_odds(odds)
    q = [1.0 / o for o in odds]
    total = sum(q)
    return [x / total for x in q]


def devig_power(odds):
    """
    Find k so that sum(q_i ** k) == 1, where q_i = 1 / odds_i.
    Takes more margin off longshots than favourites, which matches how
    books usually shade their prices better than the proportional method.
    """
    _check_odds(odds)
    q = [1.0 / o for o in odds]
    if sum(q) <= 1.0:  # no margin to remove
        return devig_proportional(odds)
    lo, hi = 1.0, 50.0
    for _ in range(100):
        mid = (lo + hi) / 2
        if sum(x ** mid for x in q) > 1.0:
            lo = mid
        else:
            hi = mid
    k = (lo + hi) / 2
    return [x ** k for x in q]


DEVIG_FUNCS = {"power": devig_power, "proportional": devig_proportional}


def min_odds(p, edge):
    """Smallest decimal odds that give at least `edge` (0.03 = 3%) at probability p."""
    return (1.0 + edge) / p


# --------------------------------------------------------------------------
# Sample data (made up: teams, leagues and prices are fictional)
# --------------------------------------------------------------------------
def sample_events(now):
    """Each event: sport, league, name, start, and a list of markets.
    Each outcome has the sharp book's odds and, optionally, Bet365's odds."""

    def at(hours):
        return (now + timedelta(hours=hours)).replace(microsecond=0)

    def out(name, sharp, bet365=None):
        return {"name": name, "sharp": sharp, "bet365": bet365}

    return [
        {"sport": "Soccer", "league": "Sample League A", "event": "Harbor FC vs Union Park",
         "start": at(3), "markets": [
             {"market": "Match result", "outcomes": [
                 out("Harbor FC", 2.10, 2.15), out("Draw", 3.45, 3.40), out("Union Park", 3.60, 3.95)]}]},
        {"sport": "Soccer", "league": "Sample League A", "event": "Alder Town vs Kestrel Rovers",
         "start": at(5), "markets": [
             {"market": "Total goals 2.5", "outcomes": [
                 out("Over 2.5", 1.95, 2.05), out("Under 2.5", 1.95, 1.80)]}]},
        {"sport": "Soccer", "league": "Sample League B", "event": "Millbrook vs Stonehaven",
         "start": at(26), "markets": [
             {"market": "Match result", "outcomes": [
                 out("Millbrook", 1.70), out("Draw", 3.90), out("Stonehaven", 5.25)]}]},

        {"sport": "Football", "league": "Sample Football League", "event": "Lakeside Pioneers vs Granite Peak Wolves",
         "start": at(20), "markets": [
             {"market": "Point spread 3.5", "outcomes": [
                 out("Lakeside Pioneers -3.5", 1.91, 1.87), out("Granite Peak Wolves +3.5", 1.95, 2.10)]},
             {"market": "Total points 44.5", "outcomes": [
                 out("Over 44.5", 1.93, 1.90), out("Under 44.5", 1.93, 1.95)]}]},

        {"sport": "Baseball", "league": "Sample Baseball League", "event": "Cedar Bay Herons vs Ridgeway Hawks",
         "start": at(6), "markets": [
             {"market": "Moneyline", "outcomes": [
                 out("Cedar Bay Herons", 1.74, 1.72), out("Ridgeway Hawks", 2.20, 2.40)]},
             {"market": "Total runs 8.5", "outcomes": [
                 out("Over 8.5", 1.87), out("Under 8.5", 2.00)]}]},

        {"sport": "Basketball", "league": "Sample Basketball League", "event": "Metro Surge vs Coastline Waves",
         "start": at(9), "markets": [
             {"market": "Moneyline", "outcomes": [
                 out("Metro Surge", 1.55, 1.53), out("Coastline Waves", 2.45, 2.60)]},
             {"market": "Point spread 6.5", "outcomes": [
                 out("Metro Surge -6.5", 1.92, 1.90), out("Coastline Waves +6.5", 1.92, 1.95)]}]},
        {"sport": "Basketball", "league": "Sample Basketball League", "event": "Summit Peaks vs Bayfront Gulls",
         "start": at(11), "markets": [
             {"market": "Total points 224.5", "outcomes": [
                 out("Over 224.5", 1.90, 2.05), out("Under 224.5", 1.96, 1.85)]}]},

        {"sport": "Hockey", "league": "Sample Hockey League", "event": "Frostline Pines vs Copper Harbor",
         "start": at(8), "markets": [
             {"market": "Moneyline", "outcomes": [
                 out("Frostline Pines", 1.85, 1.83), out("Copper Harbor", 2.10, 2.25)]},
             {"market": "Total goals 5.5", "outcomes": [
                 out("Over 5.5", 2.02, 2.00), out("Under 5.5", 1.86, 1.85)]}]},
    ]


# --------------------------------------------------------------------------
# Config and API key
# --------------------------------------------------------------------------
def load_config():
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))  # deep copy
    if CONFIG_PATH.exists():
        try:
            user = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
        except json.JSONDecodeError as e:
            raise SystemExit(f"config.json isn't valid JSON: {e}")
        for k, v in user.items():
            if k == "tournaments" and isinstance(v, dict):
                cfg["tournaments"].update(v)
            else:
                cfg[k] = v
    env_base = os.environ.get("ODDSPAPI_BASE_URL")
    if env_base:
        cfg["base_url"] = env_base
    return cfg


def _read_dotenv():
    for folder in (HERE, Path.cwd()):
        path = folder / ".env"
        if path.exists():
            for line in path.read_text(encoding="utf-8").splitlines():
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, v = line.split("=", 1)
                if k.strip() == "ODDSPAPI_KEY":
                    return v.strip().strip('"').strip("'")
    return None


def _clean_key(key):
    """Removes spaces, line breaks and quote marks around a pasted key (a common copy-and-paste slip)."""
    if not key:
        return None
    return key.strip().strip("\"'").strip() or None


def get_api_key():
    key = os.environ.get("ODDSPAPI_KEY") or _read_dotenv()
    if not key and sys.stdin.isatty():
        key = getpass.getpass("Paste your OddsPapi key (it won't be shown or saved): ")
    return _clean_key(key)


# --------------------------------------------------------------------------
# OddsPapi v4 client (standard library only)
# --------------------------------------------------------------------------
class ApiError(Exception):
    pass


class Client:
    """
    OddsPapi v4 wants the key as the `apiKey` query parameter. The key is added
    when the request is sent and is never printed, so it can't leak into messages.

    Rules from their docs that this client follows:
      * 1 request = 1 call to a billable endpoint, whatever it returns (/v4/account is free)
      * every endpoint has a 1000 ms cooldown, so calls are spaced by `gap` seconds
    """

    def __init__(self, key, base_url, max_requests, gap=1.1, retry_wait=5.0):
        self.key = key
        self.retry_wait = retry_wait
        self.base = base_url.rstrip("/")
        self.max_requests = max_requests
        self.gap = gap
        self.count = 0
        self._last = 0.0

    def get(self, path, params=None, gap=None):
        billable = path != "/v4/account"
        query = {k: v for k, v in (params or {}).items() if v is not None}
        query["apiKey"] = self.key
        url = f"{self.base}{path}?{urllib.parse.urlencode(query)}"
        req = urllib.request.Request(url, headers={"Accept": "application/json", "User-Agent": "edge-scanner/1.0"})

        for attempt in range(3):
            if billable and self.count >= self.max_requests:
                raise ApiError(f"Stopped: reached max_requests_per_run ({self.max_requests}) in config.json.")
            pause = (self.gap if gap is None else gap) - (time.monotonic() - self._last)
            if pause > 0:
                time.sleep(pause)
            if billable:
                self.count += 1
            try:
                with urllib.request.urlopen(req, timeout=30) as resp:
                    self._last = time.monotonic()
                    return json.loads(resp.read().decode("utf-8"))
            except urllib.error.HTTPError as e:
                self._last = time.monotonic()
                body = e.read().decode("utf-8", "replace")
                if e.code == 401:
                    raise ApiError(
                        "OddsPapi rejected the key (401). Re-copy it from oddspapi.io/en/account and make sure "
                        "there are no extra spaces. (Pasting is invisible, so try again or use a .env file.)")
                if e.code == 429:
                    if "REQUEST_LIMIT_EXCEEDED" in body:
                        raise ApiError("Your OddsPapi request allowance for this period is used up. "
                                       "Check usage with --check; it resets with your plan.")
                    if attempt < 2:
                        time.sleep(2)
                        continue
                if e.code >= 500:
                    # OddsPapi's own servers hiccup now and then. The free account call is retried twice; calls that
                    # use up requests (they're counted even when they fail) are retried once.
                    if attempt + 1 < (2 if billable else 3):
                        time.sleep(self.retry_wait * (attempt + 1))
                        continue
                    raise ApiError(f"OddsPapi had a server problem (HTTP {e.code} from {path}). It's usually temporary: "
                                   f"wait a few minutes and run again. Details: {body[:200]}")
                raise ApiError(f"HTTP {e.code} from {path}: {body[:300]}")
            except urllib.error.URLError as e:
                raise ApiError(f"Couldn't reach OddsPapi: {e.reason}")
            except json.JSONDecodeError:
                raise ApiError(f"OddsPapi returned something that isn't JSON for {path}.")
        raise ApiError(f"Gave up on {path} after repeated rate-limit responses.")


def make_client(cfg):
    key = get_api_key()
    if not key:
        raise SystemExit(
            "No API key found. Set ODDSPAPI_KEY, or create a file named .env next to this script "
            "containing:  ODDSPAPI_KEY=your-key")
    looks_ok = re.fullmatch(r"[0-9a-fA-F]{8}(-[0-9a-fA-F]{4}){3}-[0-9a-fA-F]{12}", key) is not None
    print(f"API key found: {len(key)} characters"
          + ("" if looks_ok else " (keys usually look like xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx, 36 characters; "
                                 "check it for typos or missing parts)"))
    return Client(key, cfg["base_url"], int(cfg["max_requests_per_run"]), float(cfg.get("request_gap_seconds", 1.1)),
                  float(cfg.get("retry_wait_seconds", 5)))


def get_subscription(client):
    """Account info is free (not counted). Returns the active subscription dict, or {}."""
    data = client.get("/v4/account")
    subs = data.get("subscriptions") or []
    current = data.get("current_subscription_id")
    for s in subs:
        if s.get("subscription_id") == current:
            return s
    for s in subs:
        if s.get("is_active"):
            return s
    return subs[0] if subs else {}


def quota_text(sub):
    limit, used = sub.get("request_limit"), sub.get("request_count")
    if isinstance(limit, (int, float)) and isinstance(used, (int, float)):
        return f"{int(used)} of {int(limit)} requests used ({int(limit - used)} left)"
    return "quota not shown by the API"


# --------------------------------------------------------------------------
# Setup commands
def cmd_diagnose(cfg):
    """Sends three small, free requests and prints how OddsPapi answers each (never prints the key).
    Meant to be run from GitHub Actions to find out why a run that works on your computer fails there."""
    import platform
    base = cfg["base_url"].rstrip("/")
    key = get_api_key()
    print(f"Python {platform.python_version()} on {platform.system()}")
    if key:
        ok = re.fullmatch(r"[0-9a-fA-F]{8}(-[0-9a-fA-F]{4}){3}-[0-9a-fA-F]{12}", key) is not None
        print(f"API key found: {len(key)} characters, format {'looks right' if ok else 'is unusual'}")
    else:
        print("No API key found (is the ODDSPAPI_KEY secret set, with exactly that name?)")

    def probe(label, k, agent):
        url = f"{base}/v4/account?" + urllib.parse.urlencode({"apiKey": k})
        req = urllib.request.Request(url, headers={"Accept": "application/json", "User-Agent": agent})
        try:
            with urllib.request.urlopen(req, timeout=30) as r:
                status, body = r.status, r.read().decode("utf-8", "replace")
        except urllib.error.HTTPError as e:
            status, body = e.code, e.read().decode("utf-8", "replace")
        except urllib.error.URLError as e:
            print(f"  {label}: could not connect ({e.reason})")
            return
        if status == 200:
            try:
                subs = json.loads(body).get("subscriptions") or [{}]
                detail = quota_text(subs[0])
            except (ValueError, AttributeError):
                detail = ""
            print(f"  {label}: HTTP 200, works. {detail}")      # the body itself is not printed: it contains the key
        else:
            print(f"  {label}: HTTP {status}. {body[:160]}")
        time.sleep(1.2)

    print("Probes (the account call is free):")
    if key:
        probe("1. your key, normal request", key, "edge-scanner/1.0")
    probe("2. a made-up key", "00000000-0000-0000-0000-000000000000", "edge-scanner/1.0")
    if key:
        probe("3. your key, browser-style request", key, "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/124 Safari/537.36")



# --------------------------------------------------------------------------
ID_TO_SPORT = {v: k for k, v in SPORT_IDS.items()}


def cmd_check(client, cfg):
    sub = get_subscription(client)
    print("Your key works. This check is free: it doesn't use up any requests.")
    print(f"  Plan active: {sub.get('is_active')}. {quota_text(sub)}.")
    if sub.get("valid_until"):
        print(f"  Plan valid until: {sub['valid_until']}")
    ids = sub.get("sport_ids")
    if ids:
        names = [ID_TO_SPORT.get(i) for i in SPORT_IDS.values() if i in ids]
        missing = [s for s, i in SPORT_IDS.items() if i not in ids]
        print(f"  Your five sports on the plan: {', '.join(n for n in names if n) or 'none'}"
              + (f". NOT included: {', '.join(missing)}" if missing else ""))
    books = sub.get("bookmakers")
    if isinstance(books, dict) and books:
        print(f"  Bookmakers on your plan: {', '.join(sorted(books))}")
        for slug in dict.fromkeys(b for b in (cfg["sharp_book"], cfg.get("compare_book"), "bet365") if b):
            print(f"    {slug}: {'included' if slug in books else 'NOT included on your plan'}")
    else:
        print("  The API didn't list your bookmakers. The first live run will show which ones return prices.")


def cmd_find_tournaments(client, cfg, sport=None, search=""):
    sports = [sport] if sport else SPORTS
    terms = [t.strip() for t in search.lower().split(",") if t.strip()]
    for sp in sports:
        data = client.get("/v4/tournaments", {"sportId": SPORT_IDS[sp]})
        data = data if isinstance(data, list) else []
        by_id = {t.get("tournamentId"): t for t in data}
        print(f"\n{sp} (sportId {SPORT_IDS[sp]}): {len(data)} tournaments. Columns: id, name, upcoming games, later games")
        shown = 0
        for t in sorted(data, key=lambda x: -((x.get("upcomingFixtures") or 0) + (x.get("futureFixtures") or 0))):
            text = f'{t.get("tournamentName", "")} {t.get("categoryName") or ""} {t.get("tournamentSlug") or ""}'.lower()
            if terms and not any(t in text for t in terms):
                continue
            print(f'  {t["tournamentId"]:>8}  {t.get("tournamentName")} ({t.get("categoryName")})'
                  f'  {t.get("upcomingFixtures", "?")}  {t.get("futureFixtures", "?")}')
            shown += 1
            if shown >= 60 and not terms:
                print("  ... (use --search to narrow the list)")
                break
        if terms and not shown:
            print("  (nothing matches that search)")
        for t in cfg["tournaments"].get(sp, []):
            real = by_id.get(t["id"])
            if real is None:
                print(f'  CONFIG CHECK: id {t["id"]} ("{t.get("name")}") was not found for {sp}. Fix it in config.json.')
            else:
                print(f'  CONFIG CHECK: id {t["id"]} is "{real.get("tournamentName")}" '
                      f'(config calls it "{t.get("name")}")')
    print("\nAdd the ones you want to config.json, like:")
    print('  "Soccer": [{"id": 123, "name": "League name"}]')
    print(f"Requests used this run: {client.count}")


def _market_name(m):
    return str(m.get("marketName") or m.get("name") or "")


def classify_market(m, sport):
    """Map OddsPapi's marketType (as listed by --find-markets) to the types this tool uses.
    Returns None for markets the tool ignores (team totals, player props, halves are filtered later by period)."""
    api_type = m.get("marketType")
    names = {str(o.get("outcomeName")).lower() for o in m.get("outcomes", [])}
    if api_type == "bothteamsscore" or (api_type == "totals" and "both teams to score" in _market_name(m).lower()):
        return "btts" if sport == "Soccer" and names == {"yes", "no"} else None
    if api_type == "totals-corners":
        return "corners_totals" if sport == "Soccer" and names == {"over", "under"} else None
    if api_type == "1x2-corners":
        return "corners_1x2" if sport == "Soccer" and names == {"1", "x", "2"} else None
    if api_type in ("moneyline", "1x2", "drawnobet", "spreads"):
        return api_type
    if api_type == "totals":
        return "totals" if names == {"over", "under"} else None
    return None


def cmd_build_markets(client, cfg):
    data = client.get("/v4/markets")
    cache = {"markets": {}}
    kept, by_type = Counter(), Counter()
    for m in data if isinstance(data, list) else []:
        sport = ID_TO_SPORT.get(m.get("sportId"))
        if not sport or m.get("playerProp"):
            continue
        mtype = classify_market(m, sport)
        if not mtype:
            continue
        cache["markets"][str(m["marketId"])] = {
            "sport": sport, "name": _market_name(m), "type": mtype, "api_type": m.get("marketType"),
            "period": m.get("period"), "handicap": m.get("handicap"),
            "outcomes": [{"id": o["outcomeId"], "name": o.get("outcomeName")} for o in m.get("outcomes", [])],
        }
        kept[sport] += 1
        by_type[(sport, mtype)] += 1
    cache["built_at"] = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    MARKETS_CACHE_PATH.write_text(json.dumps(cache), encoding="utf-8")
    for sp in SPORTS:
        print(f"  {sp}: kept {kept[sp]} market definitions")
    extras = {t: by_type[("Soccer", t)] for t in ("btts", "corners_totals", "corners_1x2")}
    print(f"  Soccer extras: {extras}")
    print(f"Saved to {MARKETS_CACHE_PATH.name}. Requests used this run: {client.count}")


def cmd_find_bookmakers(client, cfg, search):
    """Lists OddsPapi bookmakers whose name or slug contains any comma-separated search word (1 request)."""
    terms = [t.strip() for t in search.lower().split(",") if t.strip()]
    data = client.get("/v4/bookmakers")
    data = data if isinstance(data, list) else []
    print(f"OddsPapi lists {len(data)} bookmakers.")
    shown = 0
    for b in sorted(data, key=lambda x: str(x.get("bookmakerName")).lower()):
        text = f'{b.get("bookmakerName", "")} {b.get("slug", "")} {b.get("cloneOf") or ""}'.lower()
        if terms and not any(t in text for t in terms):
            continue
        clone = f'  (clone of {b["cloneOf"]})' if b.get("cloneOf") else ""
        print(f'  {str(b.get("slug")):<26} {b.get("bookmakerName")}{clone}')
        shown += 1
        if shown >= 60:
            print("  ... (narrow the search to see the rest)")
            break
    if terms and not shown:
        print("  (no bookmaker matches that search)")
    print("Being listed doesn't mean your plan includes it: --check shows the bookmakers on your plan.")
    print(f"Requests used this run: {client.count}")


def cmd_find_markets(client, cfg, search, sport=None):
    """Prints markets whose name contains any of the comma-separated search words. Costs 1 request."""
    terms = [t.strip() for t in search.lower().split(",") if t.strip()]
    if not terms:
        raise SystemExit('Tell me what to look for, for example:  --find-markets "corner,both teams"')
    data = client.get("/v4/markets")
    data = data if isinstance(data, list) else []
    types_seen = Counter(m.get("marketType") for m in data if ID_TO_SPORT.get(m.get("sportId")))
    print("Market types in the catalog (for your five sports):", dict(types_seen))
    shown = Counter()
    for m in data:
        sp = ID_TO_SPORT.get(m.get("sportId"))
        if not sp or (sport and sp != sport) or m.get("playerProp"):
            continue
        name = _market_name(m)
        if not any(t in name.lower() for t in terms):
            continue
        shown[sp] += 1
        if shown[sp] > 40:
            continue
        outs = "/".join(str(o.get("outcomeName")) for o in m.get("outcomes", []))
        print(f'  {sp:<10} id {m.get("marketId"):<7} type={m.get("marketType")} period={m.get("period")} '
              f'handicap={m.get("handicap")}  "{name}"  outcomes: {outs}')
    for sp, n in shown.items():
        if n > 40:
            print(f"  ({sp}: {n - 40} more not shown; narrow the search or use --sport)")
    if not shown:
        print("  (no markets matched)")
    print(f"Requests used this run: {client.count}")


def cmd_build_participants(client, cfg, sport=None):
    if sport:
        sports = [sport]
    else:
        sports = [s for s in SPORTS if cfg["tournaments"].get(s)] or SPORTS
    cache = {}
    if PARTICIPANTS_CACHE_PATH.exists():
        try:
            cache = json.loads(PARTICIPANTS_CACHE_PATH.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            cache = {}
    for sp in sports:
        data = client.get("/v4/participants", {"sportId": SPORT_IDS[sp]})
        cache[sp] = {str(k): v for k, v in data.items()} if isinstance(data, dict) else {}
        print(f"  {sp}: {len(cache[sp])} team names")
    PARTICIPANTS_CACHE_PATH.write_text(json.dumps(cache, ensure_ascii=False), encoding="utf-8")
    print(f"Saved to {PARTICIPANTS_CACHE_PATH.name}. Requests used this run: {client.count}")


# --------------------------------------------------------------------------
# Live data
# --------------------------------------------------------------------------
def _line(h):
    return f"{h:g}"


def _signed(h):
    return f"{h:+g}"


def _quarter(h):
    """Quarter lines (x.25 / x.75) split a bet across two lines, so the min-odds math is only approximate."""
    return " (quarter line)" if h is not None and abs(h * 2 - round(h * 2)) > 1e-9 else ""


def market_label(m, sport):
    t, h = m["type"], m.get("handicap")
    if t == "moneyline":
        return "Moneyline"
    if t == "1x2":
        return "Match result" if sport == "Soccer" else "3-way result (regulation time)"
    if t == "drawnobet":
        return "Draw no bet"
    if t == "btts":
        return "Both teams to score"
    if t == "corners_1x2":
        return "Most corners"
    if t == "corners_totals" and h is not None:
        return f"Corners total {_line(h)}{_quarter(h)}"
    if t == "totals" and h is not None:
        return f"Total {_line(h)}{_quarter(h)}"
    if t == "spreads" and h is not None:
        return f"Spread {_signed(h)} (first-listed team){_quarter(h)}"
    return None


def outcome_label(m, name, p1, p2):
    t, h = m["type"], m.get("handicap")
    name = str(name)
    if t in ("moneyline", "1x2", "drawnobet"):
        return {"1": p1, "2": p2, "X": "Draw"}.get(name, name)
    if t == "btts":
        return f"BTTS {name}"
    if t == "corners_totals":
        return f"Corners {name} {_line(h)}"
    if t == "corners_1x2":
        return {"1": f"{p1} (most corners)", "X": "Equal corners", "2": f"{p2} (most corners)"}.get(name, name)
    if t == "totals":
        return f"{name} {_line(h)}"
    if t == "spreads":
        # ASSUMPTION to verify against a real book before enabling spreads:
        # the handicap belongs to participant 1, and participant 2 gets the opposite sign.
        if name == "1":
            return f"{p1} {_signed(h)}"
        if name == "2":
            return f"{p2} {_signed(-h)}"
    return name


TYPE_ORDER = {"moneyline": 0, "1x2": 0, "drawnobet": 1, "spreads": 2, "totals": 3, "btts": 4,
              "corners_1x2": 5, "corners_totals": 6}


def _book_markets(block):
    """From one bookmaker's block, return {marketId: {"active", "outcomes": {outcomeId: price info}}}.
    Only normal (non-player) prices are kept."""
    out = {}
    for mid, m in ((block or {}).get("markets") or {}).items():
        try:
            mid_i = int(mid)
        except (TypeError, ValueError):
            continue
        outs = {}
        for oid, o in ((m or {}).get("outcomes") or {}).items():
            player = (((o or {}).get("players")) or {}).get("0")
            price = (player or {}).get("price")
            if not isinstance(price, (int, float)) or price <= 1.0:
                continue
            try:
                outs[int(oid)] = {"price": float(price), "active": player.get("active") is not False,
                                  "mainLine": player.get("mainLine")}
            except (TypeError, ValueError):
                continue
        out[mid_i] = {"active": (m or {}).get("marketActive") is not False, "outcomes": outs}
    return out


def _parse_time(s):
    return datetime.fromisoformat(str(s).replace("Z", "+00:00")).astimezone(timezone.utc)


def fixture_to_event(fx, sport, cfg, markets, names, tournament_names, now, stats, extra_books=()):
    """Turn one fixture from /v4/odds-by-tournaments into the same event shape the sample data uses."""
    if fx.get("statusId") not in (0, 1) or fx.get("hasOdds") is False:
        stats["skipped: not an upcoming game with odds"] += 1
        return None
    try:
        start = _parse_time(fx["startTime"])
    except (KeyError, ValueError):
        stats["skipped: bad start time"] += 1
        return None
    if start < now + timedelta(minutes=cfg["min_minutes_to_start"]):
        stats["skipped: started or starting very soon"] += 1
        return None

    def team(pid):
        name = names.get(str(pid))
        if not name:
            stats["team names missing (run --build-participants)"] += 1
            return f"Team {pid}"
        return name

    p1, p2 = team(fx.get("participant1Id")), team(fx.get("participant2Id"))

    sharp, compare = cfg["sharp_book"], cfg.get("compare_book")
    books = fx.get("bookmakerOdds") or {}

    def problem(slug):
        b = books.get(slug)
        if b is None:
            return "no prices"
        if b.get("bookmakerIsActive") is False:
            return "inactive"
        if b.get("suspended"):
            return "suspended"
        return None

    why = problem(sharp)
    if why:
        stats[f"skipped: sharp book {why}"] += 1
        return None
    sharp_m = _book_markets(books[sharp])
    comp_m = _book_markets(books[compare]) if compare and problem(compare) is None else {}
    extra_m = {slug: _book_markets(books[slug]) for slug in extra_books if slug in books and problem(slug) is None}

    out_markets = []
    ml_prices, spread_h = None, None
    for market_id, sm in sharp_m.items():
        m = markets.get(str(market_id))
        if m is None:
            stats["skipped market: not in markets_cache.json"] += 1
            continue
        if m["type"] not in cfg["market_types"]:
            stats["skipped market: type not enabled"] += 1
            continue
        if m.get("period") not in cfg["periods"]:
            stats[f"skipped market: period '{m.get('period')}' not enabled"] += 1
            continue
        ids = [o["id"] for o in m["outcomes"]]
        if not sm["active"] or not ids or any(i not in sm["outcomes"] or not sm["outcomes"][i]["active"] for i in ids):
            stats["skipped market: inactive or incomplete at sharp book"] += 1
            continue
        flags = [sm["outcomes"][i]["mainLine"] for i in ids]
        if m["type"] in ("totals", "spreads", "corners_totals"):
            if not all(f is True for f in flags):
                stats["skipped market: not the main line"] += 1
                continue
        elif any(f is False for f in flags):
            stats["skipped market: not the main line"] += 1
            continue
        label = market_label(m, sport)
        if label is None:
            stats["skipped market: no label"] += 1
            continue
        cm = comp_m.get(market_id)
        outcomes = []
        for o in m["outcomes"]:
            cq = cm["outcomes"].get(o["id"]) if cm and cm["active"] else None
            if cq and not cq["active"]:
                cq = None
            item = {
                "name": outcome_label(m, o["name"], p1, p2),
                "outcome_id": o["id"],
                "sharp": sm["outcomes"][o["id"]]["price"],
                "bet365": cq["price"] if cq else None,
            }
            if extra_books:
                others = {}
                for slug in extra_books:
                    xm = extra_m.get(slug, {}).get(market_id)
                    xq = xm["outcomes"].get(o["id"]) if xm and xm["active"] else None
                    others[slug] = xq["price"] if xq and xq["active"] else None
                item["others"] = others
            outcomes.append(item)
        stats["markets kept"] += 1
        if m["type"] in ("moneyline", "1x2"):
            by_name = {str(o["name"]): sm["outcomes"][o["id"]]["price"] for o in m["outcomes"]}
            if "1" in by_name and "2" in by_name:
                ml_prices = (by_name["1"], by_name["2"])
        elif m["type"] == "spreads" and m.get("handicap") not in (None, 0):
            spread_h = m["handicap"]
        if any(o["bet365"] is not None for o in outcomes):
            stats["markets with a Bet365 price"] += 1
        out_markets.append(((TYPE_ORDER.get(m["type"], 9), m.get("handicap") or 0),
                            {"market": label, "market_id": market_id, "outcomes": outcomes}))

    if not out_markets:
        stats["skipped: no usable markets"] += 1
        return None
    if ml_prices and spread_h is not None and max(ml_prices) / min(ml_prices) > 1.05:
        # The team with the negative handicap should be the favorite (the shorter moneyline price).
        ok = (spread_h < 0) == (ml_prices[0] < ml_prices[1])
        stats["spread sign check: matches the favorite" if ok else "spread sign check: does NOT match the favorite"] += 1
    out_markets.sort(key=lambda x: x[0])
    stats["fixtures kept"] += 1
    return {
        "sport": sport,
        "league": tournament_names.get(fx.get("tournamentId")) or f"Tournament {fx.get('tournamentId')}",
        "event": f"{p1} vs {p2}",
        "fixture_id": fx.get("fixtureId"),
        "start": start,
        "markets": [mk for _, mk in out_markets],
    }


def _load_cache(path, what, fix):
    if not path.exists():
        raise SystemExit(f"{path.name} is missing ({what}). Run:  python edge_scanner.py {fix}")
    return json.loads(path.read_text(encoding="utf-8"))


MAX_TOURNAMENTS_PER_REQUEST = 5   # OddsPapi rejects more than 5 tournament IDs in one request


def _chunks(items, n):
    return [items[i:i + n] for i in range(0, len(items), n)]


def _fetch_book(client, tournaments, slug):
    """OddsPapi v4 takes exactly one bookmaker per call, in the `bookmaker` parameter.
    A 404 FIXTURE_NOT_FOUND just means nothing is scheduled for those leagues (off-season, break), so it gives []."""
    try:
        data = client.get("/v4/odds-by-tournaments", {
            "tournamentIds": ",".join(str(t["id"]) for t in tournaments),
            "bookmaker": slug,
        })
    except ApiError as e:
        if "FIXTURE_NOT_FOUND" in str(e):
            return []
        raise
    if isinstance(data, list):
        return data
    return [data] if isinstance(data, dict) and data.get("fixtureId") else []


def live_events(now, cfg, client):
    markets = _load_cache(MARKETS_CACHE_PATH, "market definitions", "--build-markets").get("markets", {})
    participants = _load_cache(PARTICIPANTS_CACHE_PATH, "team names", "--build-participants")
    sharp, compare = cfg["sharp_book"], cfg.get("compare_book")

    plan = [(sp, cfg["tournaments"][sp]) for sp in SPORTS if cfg["tournaments"].get(sp)]
    if not plan:
        raise SystemExit("No tournaments in config.json yet. Run --find-tournaments and add some IDs.")
    t_sport = {t["id"]: sp for sp, ts in plan for t in ts}
    t_names = {t["id"]: t.get("name") for sp, ts in plan for t in ts}
    groups = []
    if cfg.get("combine_sports"):
        # pack leagues from every sport together, 5 per request
        parts = _chunks([t for _, ts in plan for t in ts], MAX_TOURNAMENTS_PER_REQUEST)
        groups = [("all sports" if len(parts) == 1 else f"all sports, part {i}", c) for i, c in enumerate(parts, 1)]
    else:
        # one request per sport, or two or more when a sport has more than 5 leagues
        for sp, ts in plan:
            parts = _chunks(ts, MAX_TOURNAMENTS_PER_REQUEST)
            groups += [(sp if len(parts) == 1 else f"{sp}, part {i}", c) for i, c in enumerate(parts, 1)]

    by_sport_cmp, default_cmp = compare_settings(cfg)
    cmp_sports = None if default_cmp is not None else set(by_sport_cmp)     # None = every sport gets estimates

    def wants_compare(tournaments):
        return bool(compare) and (cmp_sports is None or any(t_sport.get(t["id"]) in cmp_sports for t in tournaments))

    sharp_extras = [b for b in dict.fromkeys(cfg.get("sharp_extra_books") or []) if b and b not in (sharp, compare)]
    needed = len(groups) * (1 + len(sharp_extras)) + sum(1 for _, ts in groups if wants_compare(ts))
    if needed > client.max_requests:
        raise SystemExit(f"This run needs {needed} requests but max_requests_per_run is {client.max_requests}. "
                         "Remove a sport or raise the limit in config.json.")

    try:
        sub = get_subscription(client)                   # free, and only used for the quota check
    except ApiError as e:
        print(f"Couldn't read your account info ({e}). Carrying on without the quota check.")
        sub = {}
    limit, used = sub.get("request_limit"), sub.get("request_count")
    if isinstance(limit, (int, float)) and isinstance(used, (int, float)) and limit - used < needed:
        raise SystemExit(f"Only {int(limit - used)} requests left on your plan and this run needs {needed}. "
                         "Stopping so nothing is wasted.")
    if sub:
        print(f"Before this run: {quota_text(sub)}. This run will use up to {needed}.")

    stats = Counter()
    events = []
    compare_ok = bool(compare)
    active_extras = list(sharp_extras)
    for label, tournaments in groups:
        fixtures = _fetch_book(client, tournaments, sharp)
        note = ""
        for slug in list(active_extras) if fixtures else []:
            try:
                extra = {f.get("fixtureId"): f for f in _fetch_book(client, tournaments, slug)}
                for fx in fixtures:
                    block = ((extra.get(fx.get("fixtureId")) or {}).get("bookmakerOdds") or {}).get(slug)
                    if block is not None:
                        fx.setdefault("bookmakerOdds", {})[slug] = block
                note += f" (+{slug})"
            except ApiError as e:
                if not str(e).startswith("HTTP 4") or str(e).startswith("HTTP 429"):
                    raise
                print(f"  {label}: couldn't get {slug} ({e}). Carrying on without it.")
                active_extras.remove(slug)
        if compare_ok and fixtures and wants_compare(tournaments):
            try:
                extra = {f.get("fixtureId"): f for f in _fetch_book(client, tournaments, compare)}
                for fx in fixtures:
                    other = extra.get(fx.get("fixtureId"))
                    if other:
                        fx.setdefault("bookmakerOdds", {}).update(other.get("bookmakerOdds") or {})
                note = f" (+{compare})"
            except ApiError as e:
                if not str(e).startswith("HTTP 4") or str(e).startswith("HTTP 429"):
                    raise
                print(f"  {label}: couldn't get {compare} ({e}). Carrying on without it.")
                compare_ok = False
        print(f"  {label}: {len(fixtures)} fixtures returned for {len(tournaments)} tournament(s){note}")
        stats["fixtures returned"] += len(fixtures)
        for fx in fixtures:
            sp = t_sport.get(fx.get("tournamentId")) or ID_TO_SPORT.get(fx.get("sportId"))
            if not sp:
                stats["skipped: tournament not in config.json"] += 1
                continue
            ev = fixture_to_event(fx, sp, cfg, markets, participants.get(sp, {}), t_names, now, stats,
                                  extra_books=active_extras)
            if ev:
                if cmp_sports is not None and sp not in cmp_sports:
                    for mk in ev["markets"]:             # the factor wasn't measured for this sport, so don't use it
                        for o in mk["outcomes"]:
                            o["bet365"] = None
                events.append(ev)

    print("\nWhat happened to the data:")
    for k in sorted(stats):
        print(f"  {k}: {stats[k]}")
    good, bad = stats["spread sign check: matches the favorite"], stats["spread sign check: does NOT match the favorite"]
    if bad and bad >= good:
        print("\nWARNING: the spread signs look REVERSED compared with the moneyline favorites. "
              "Don't use the spread picks until this is fixed. Tell me and I'll correct it.")
    elif bad:
        print(f"\nNote: {bad} spread line(s) didn't match the moneyline favorite. That can happen, "
              "so check those against your book before betting.")
    try:
        print(f"After this run: {quota_text(get_subscription(client))}.")
    except ApiError:
        pass
    return events


# --------------------------------------------------------------------------
# Build rows and write the page
# --------------------------------------------------------------------------
def build_rows(events, devig, sharp_extra=(), main_slug="pinnacle", weights=None):
    """One row per selection. The true probability is the weighted average of each sharp book's no-vig probability
    (the main book counts 2, each extra book 1, unless `weights` says otherwise). A book only counts for a market
    when it prices every outcome of it. `p_range` is how far apart the books are, as a fraction (0.02 = 2 points)."""
    weights = weights or {}

    def weight(slug, default):
        w = weights.get(slug)
        return float(w) if isinstance(w, (int, float)) and w > 0 else default

    rows = []
    for ev in events:
        for mkt in ev["markets"]:
            outcomes = mkt["outcomes"]
            main_probs = devig([o["sharp"] for o in outcomes])
            books = [(main_probs, weight(main_slug, 2.0))]
            for slug in sharp_extra:
                prices = [(o.get("others") or {}).get(slug) for o in outcomes]
                if all(isinstance(x, (int, float)) and x > 1.0 for x in prices):
                    books.append((devig(prices), weight(slug, 1.0)))
            total_w = sum(w for _, w in books)
            for i, o in enumerate(outcomes):
                per_book = [pb[i] for pb, _ in books]
                p = sum(pb[i] * w for pb, w in books) / total_w
                others = {k: v for k, v in (o.get("others") or {}).items() if k not in sharp_extra}
                rows.append({
                    "id": f'{ev["event"]}|{mkt["market"]}|{o["name"]}',
                    "sport": ev["sport"],
                    "league": ev["league"],
                    "event": ev["event"],
                    "fixture_id": ev.get("fixture_id"),
                    "market_id": mkt.get("market_id"),
                    "outcome_id": o.get("outcome_id"),
                    "start": ev["start"].astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                    "market": mkt["market"],
                    "selection": o["name"],
                    "sharp": o["sharp"],
                    "p": round(p, 5),
                    "fair": round(1.0 / p, 3),
                    "p_main": round(main_probs[i], 5),
                    "n_books": len(books),
                    "p_range": round(max(per_book) - min(per_book), 5),
                    "bet365": o.get("bet365"),
                    **({"others": others} if others else {}),
                })
    return rows


def compare_settings(cfg):
    """Returns (by_sport, default). Each is {"factor": f, "spread": s} with the spread as a fraction (0.03 = 3%).
    Sports in by_sport were measured; `default` (or None) is used for the rest. Older single-setting configs still work."""
    def one(d):
        return {"factor": float(d.get("factor") or 1.0), "spread": float(d.get("spread_pct") or 0.0) / 100.0}
    by = {sp: one(v) for sp, v in (cfg.get("compare_by_sport") or {}).items()}
    default = one(cfg["compare_default"]) if cfg.get("compare_default") else None
    if not by and default is None and cfg.get("compare_book"):
        legacy = {"factor": cfg.get("compare_factor"), "spread_pct": cfg.get("compare_spread_pct")}
        by = {sp: one(legacy) for sp in (cfg.get("compare_sports") or SPORTS)}
    return by, default


def compare_info(cfg):
    """What the page needs to know about the comparison book (None when none is configured)."""
    if not cfg.get("compare_book"):
        return None
    by, default = compare_settings(cfg)
    return {"label": cfg.get("compare_label") or cfg["compare_book"],
            "your_book": cfg.get("your_book_label") or "your book",
            "by_sport": by, "default": default}


def write_page(rows, source, devig_name, out_path, sharp_label=SHARP_BOOK, password=None, compare=None):
    now = datetime.now(timezone.utc)
    sports = list(SPORTS)   # the page greys out sports that have no games in this data
    data = {
        "generated_at": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "source": source,
        "sharp_book": sharp_label,
        "devig": DEVIG_LABELS[devig_name],
        "sports": sports,
        "compare": compare,
        "rows": rows,
    }
    # "<" is escaped so team names can never close the <script> tag.
    payload = json.dumps(data, ensure_ascii=False).replace("<", "\\u003c")

    template = (HERE / "template.html").read_text(encoding="utf-8")
    if "__DATA_JSON__" not in template:
        raise SystemExit("template.html is missing the __DATA_JSON__ placeholder.")
    page = template.replace("__DATA_JSON__", payload)
    if password:
        page = lock_page(page, password)
    Path(out_path).write_text(page, encoding="utf-8")


# --------------------------------------------------------------------------
# Book comparison (which bookmaker's prices move most like yours?)
# --------------------------------------------------------------------------
COMPARE_TEMPLATE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="color-scheme" content="light dark">
<title>Which book prices like yours?</title>
<style>
  :root { --chalk:#EEF2F1; --paper:#FFFFFF; --ink:#14262B; --slate:#566A6F; --rule:#D3DDDC; --accent:#2D3FE0; --pine:#17784A; --pine-wash:#E3F3EA; --brick:#B3402F; }
  @media (prefers-color-scheme: dark) {
    :root { --chalk:#0E1A1D; --paper:#15262A; --ink:#E6EEEE; --slate:#9BAFB3; --rule:#2A3D41; --accent:#9AA8FF; --pine:#5CCB92; --pine-wash:#16342A; --brick:#F29A8A; }
  }
  * { box-sizing: border-box; }
  body { margin:0; padding:18px; background:var(--chalk); color:var(--ink); font:16px/1.45 system-ui,-apple-system,"Segoe UI",Roboto,Helvetica,Arial,sans-serif; font-variant-numeric: tabular-nums; }
  main { max-width: 1180px; margin: 0 auto; }
  h1 { font-size:1.5rem; margin:0 0 6px; }
  h2 { font-size:1.05rem; margin:22px 0 8px; }
  p { margin:0 0 10px; color:var(--slate); max-width: 75ch; }
  .controls { display:flex; flex-wrap:wrap; gap:12px; margin:14px 0; align-items:flex-end; }
  label { display:block; font-size:.84rem; color:var(--slate); margin-bottom:4px; }
  select, input, button { font:inherit; min-height:42px; padding:6px 10px; color:var(--ink); background:var(--paper); border:1px solid var(--rule); border-radius:8px; }
  button { cursor:pointer; }
  .wrap { background:var(--paper); border:1px solid var(--rule); border-radius:10px; overflow-x:auto; }
  table { width:100%; border-collapse:collapse; }
  th, td { padding:9px 12px; text-align:left; border-top:1px solid var(--rule); white-space:nowrap; }
  thead th { border-top:0; font-size:.84rem; font-weight:500; color:var(--slate); }
  td.r, th.r { text-align:right; }
  td small { display:block; color:var(--slate); font-size:.78rem; }
  td.pick { white-space:normal; min-width:220px; }
  td.pick b { display:block; }
  td.pick span { color:var(--slate); font-size:.84rem; }
  input.my { width:96px; text-align:right; }
  .best { color:var(--pine); font-weight:700; }
  .tag { display:inline-block; margin-left:6px; padding:1px 8px; border-radius:999px; background:var(--pine-wash); color:var(--pine); font-size:.78rem; font-weight:500; }
  .note { font-size:.9rem; }
  #stats .wrap { margin-bottom:8px; }
</style>
</head>
<body>
<main>
  <h1>Which book prices like yours?</h1>
  <p>Open your own book (Playdoit) and type its decimal odds into the last column for picks listed here: same game, same market, same line. Do at least 5, ideally 15 or more, across different games. The table at the top then shows which of the other books moves most like yours, and what scale factor turns its price into an estimate of yours. This page works on your computer only: nothing is uploaded.</p>
  <div class="controls">
    <div><label for="sport">Sport</label><select id="sport"></select></div>
    <div><label for="kind">Type of bet</label><select id="kind"></select></div>
    <div><label for="within">Starts within</label><select id="within"><option value="24">24 hours</option><option value="48" selected>48 hours</option><option value="0">Any time</option></select></div>
    <div><button id="clear" type="button">Clear my entries</button></div>
  </div>

  <section id="stats">
    <h2>Results from your entries</h2>
    <div class="wrap"><table><thead><tr>
      <th>Book</th><th class="r">Picks compared</th><th class="r">Its price vs yours (average)</th><th class="r">Spread (lower is better)</th><th class="r">Estimated yours = book price &times;</th>
    </tr></thead><tbody id="stat-rows"></tbody></table></div>
    <p class="note" id="stat-note"></p>
  </section>

  <h2>Picks</h2>
  <div class="wrap"><table><thead id="head"></thead><tbody id="rows"></tbody></table></div>
  <p class="note" id="shown"></p>
</main>

<script id="data" type="application/json">__DATA_JSON__</script>
<script>
(function () {
  "use strict";
  var DATA = JSON.parse(document.getElementById("data").textContent);
  var rows = DATA.rows, books = DATA.books, fairName = DATA.sharp_label;
  var KEY = "edge-compare-entries-v1";
  var entries = {};
  try { entries = JSON.parse(localStorage.getItem(KEY) || "{}") || {}; } catch (e) { entries = {}; }
  function save() { try { localStorage.setItem(KEY, JSON.stringify(entries)); } catch (e) { /* ignore */ } }
  function key(r) { return r.id + "@" + r.start; }

  function kind(r) {
    var m = r.market;
    if (/^(Moneyline|Match result|3-way)/.test(m)) return "Results";
    if (/^Total /.test(m)) return "Goal or point totals";
    if (/^Spread/.test(m)) return "Spreads";
    if (/^Both teams/.test(m)) return "Both teams to score";
    if (/^Corners/.test(m)) return "Corners";
    return "Other";
  }
  function el(tag, cls, text) { var n = document.createElement(tag); if (cls) n.className = cls; if (text != null) n.textContent = text; return n; }
  function fillSelect(id, values, first, preferred) {
    var s = document.getElementById(id);
    [first].concat(values).forEach(function (v) { var o = el("option", null, v); o.value = v; s.appendChild(o); });
    if (preferred && values.indexOf(preferred) !== -1) s.value = preferred;
    s.addEventListener("change", render);
  }
  var sports = []; var kinds = [];
  rows.forEach(function (r) { if (sports.indexOf(r.sport) === -1) sports.push(r.sport); var k = kind(r); if (kinds.indexOf(k) === -1) kinds.push(k); });
  fillSelect("sport", sports, "All sports");
  fillSelect("kind", kinds, "All types", "Results");
  document.getElementById("within").addEventListener("change", render);
  document.getElementById("clear").addEventListener("click", function () { entries = {}; save(); render(); });

  var timeFmt = new Intl.DateTimeFormat(undefined, { weekday: "short", hour: "numeric", minute: "2-digit" });
  function pct(x) { return (x >= 0 ? "+" : "\u2212") + Math.abs(x * 100).toFixed(1) + "%"; }

  // header
  var head = document.getElementById("head"), htr = el("tr");
  htr.appendChild(el("th", null, "Pick"));
  htr.appendChild(el("th", "r", "Fair odds (" + fairName + ")"));
  books.forEach(function (b) { htr.appendChild(el("th", "r", b)); });
  htr.appendChild(el("th", "r", "Your book's odds"));
  head.appendChild(htr);

  function render() {
    var sport = document.getElementById("sport").value, k = document.getElementById("kind").value;
    var hours = parseInt(document.getElementById("within").value, 10);
    var now = Date.now(), horizon = hours ? now + hours * 3600000 : Infinity;
    var list = rows.filter(function (r) {
      var t = new Date(r.start).getTime();
      return t > now && t <= horizon && (sport === "All sports" || r.sport === sport) && (k === "All types" || kind(r) === k);
    }).sort(function (a, b) { return new Date(a.start) - new Date(b.start); });
    var total = list.length; list = list.slice(0, 150);
    var tbody = document.getElementById("rows"); tbody.textContent = "";
    list.forEach(function (r) {
      var tr = el("tr");
      var tdp = el("td", "pick");
      tdp.appendChild(el("b", null, r.selection));
      tdp.appendChild(el("span", null, r.event + " | " + r.market + " | " + timeFmt.format(new Date(r.start))));
      tr.appendChild(tdp);
      tr.appendChild(el("td", "r", r.fair.toFixed(2)));
      books.forEach(function (b) {
        var td = el("td", "r"), p = r.others && r.others[b];
        if (p) { td.appendChild(document.createTextNode(p.toFixed(2))); td.appendChild(el("small", null, pct(p / r.fair - 1) + " vs fair")); }
        else { td.textContent = "-"; }
        tr.appendChild(td);
      });
      var tdi = el("td", "r"), inp = document.createElement("input");
      inp.className = "my"; inp.type = "number"; inp.step = "0.01"; inp.min = "1.01"; inp.setAttribute("inputmode", "decimal");
      inp.setAttribute("aria-label", "Your book's odds for " + r.selection);
      if (entries[key(r)]) inp.value = entries[key(r)];
      inp.addEventListener("input", function () {
        var v = parseFloat(inp.value);
        if (v > 1) entries[key(r)] = v; else delete entries[key(r)];
        save(); stats();
      });
      tdi.appendChild(inp); tr.appendChild(tdi);
      tbody.appendChild(tr);
    });
    document.getElementById("shown").textContent = total
      ? "Showing " + list.length + " of " + total + " picks. Change the filters to see others."
      : "No picks match these filters. Try 'Any time' or 'All types'.";
    stats();
  }

  function stats() {
    var per = {}; books.forEach(function (b) { per[b] = []; });
    var vsFair = [];
    rows.forEach(function (r) {
      var v = entries[key(r)];
      if (!(v > 1)) return;
      vsFair.push(v / r.fair);
      books.forEach(function (b) { var p = r.others && r.others[b]; if (p) per[b].push(p / v); });
    });
    var out = document.getElementById("stat-rows"); out.textContent = "";
    function mean(a) { return a.reduce(function (s, x) { return s + x; }, 0) / a.length; }
    function sd(a) { var m = mean(a); return Math.sqrt(a.reduce(function (s, x) { return s + (x - m) * (x - m); }, 0) / Math.max(1, a.length - 1)); }

    var first = el("tr");
    first.appendChild(el("td", null, "Your book vs " + fairName + " fair odds"));
    first.appendChild(el("td", "r", String(vsFair.length)));
    first.appendChild(el("td", "r", vsFair.length ? pct(mean(vsFair) - 1) : "-"));
    first.appendChild(el("td", "r", "")); first.appendChild(el("td", "r", ""));
    out.appendChild(first);

    var table = books.map(function (b) {
      var a = per[b], n = a.length;
      return { book: b, n: n, avg: n ? mean(a) : null, cv: n >= 2 ? sd(a) / mean(a) : null };
    });
    table.sort(function (x, y) {
      var xo = x.n >= 5, yo = y.n >= 5;
      if (xo !== yo) return xo ? -1 : 1;
      if (xo) return x.cv - y.cv;
      return y.n - x.n;
    });
    var best = table.length && table[0].n >= 5 ? table[0].book : null;
    table.forEach(function (t) {
      var tr = el("tr"), name = el("td", t.book === best ? "best" : null, t.book);
      if (t.book === best) name.appendChild(el("span", "tag", "closest"));
      tr.appendChild(name);
      tr.appendChild(el("td", "r", String(t.n)));
      tr.appendChild(el("td", "r", t.n ? pct(t.avg - 1) : "-"));
      tr.appendChild(el("td", "r", t.cv != null ? (t.cv * 100).toFixed(1) + "%" : "-"));
      tr.appendChild(el("td", "r", t.n >= 5 ? (1 / t.avg).toFixed(3) : "needs 5+ picks"));
      out.appendChild(tr);
    });
    var note = document.getElementById("stat-note");
    if (!vsFair.length) note.textContent = "Type your book's odds for a few picks below to see results here.";
    else if (!best) note.textContent = "Keep going: a book needs at least 5 picks that you and it both have prices for.";
    else note.textContent = "Spread under about 2% means the book moves closely with yours, so its prices make a decent filter. Over about 4% it isn't a reliable stand-in. Tell the number in the last column to whoever sets up the filter.";
  }
  render();
})();
</script>
</body>
</html>
"""


def compare_books_run(now, cfg, client, book_slug_list, sport, max_groups=None):
    """Fetch the sharp book plus each candidate book for one sport and merge their prices per selection.
    Costs (1 + number of books) requests for every group of up to 5 leagues."""
    markets = _load_cache(MARKETS_CACHE_PATH, "market definitions", "--build-markets").get("markets", {})
    participants = _load_cache(PARTICIPANTS_CACHE_PATH, "team names", "--build-participants")
    sharp = cfg["sharp_book"]
    books = [b for b in dict.fromkeys(book_slug_list) if b and b != sharp]
    if not books:
        raise SystemExit('No books to compare. Pass them like:  --compare-books "betano.mx,betcris"')
    tournaments = cfg["tournaments"].get(sport) or []
    if not tournaments:
        raise SystemExit(f"No {sport} tournaments in config.json.")
    groups = _chunks(tournaments, MAX_TOURNAMENTS_PER_REQUEST)
    if max_groups:
        groups = groups[:max_groups]
    needed = len(groups) * (1 + len(books))
    if needed > client.max_requests:
        raise SystemExit(f"This comparison needs {needed} requests (1 + {len(books)} books, for {len(groups)} group(s) of "
                         f"leagues) but max_requests_per_run is {client.max_requests}. Compare fewer books, or raise "
                         "max_requests_per_run in config.json for this one run.")
    try:
        sub = get_subscription(client)
    except ApiError:
        sub = {}
    limit, used = sub.get("request_limit"), sub.get("request_count")
    if isinstance(limit, (int, float)) and isinstance(used, (int, float)) and limit - used < needed:
        raise SystemExit(f"Only {int(limit - used)} requests left on your plan and this needs {needed}. Stopping.")
    print(f"Comparing {len(books)} books on {sport}: this will use up to {needed} requests"
          + (f" ({quota_text(sub)} before)." if sub else "."))

    cfg2 = dict(cfg, compare_book=None)
    stats, events, refused = Counter(), [], set()
    for chunk in groups:
        names = {t["id"]: t.get("name") for t in chunk}
        fixtures = _fetch_book(client, chunk, sharp)
        by_id = {f.get("fixtureId"): f for f in fixtures}
        print(f"  {', '.join(str(t.get('name', t['id'])) for t in chunk)}: {sharp} has {len(fixtures)} fixtures")
        if not fixtures:
            print("    nothing scheduled here, so the other books are skipped for this group")
            continue
        for slug in books:
            if slug in refused:
                continue
            try:
                extra = _fetch_book(client, chunk, slug)
            except ApiError as e:
                if not str(e).startswith("HTTP 4") or str(e).startswith("HTTP 429"):
                    raise
                print(f"  {slug}: refused ({e}). Skipping this book.")
                refused.add(slug)
                continue
            print(f"    {slug}: {len(extra)} fixtures")
            for f in extra:
                host = by_id.get(f.get("fixtureId"))
                block = (f.get("bookmakerOdds") or {}).get(slug)
                if host is not None and block is not None:
                    host.setdefault("bookmakerOdds", {})[slug] = block
        for fx in fixtures:
            ev = fixture_to_event(fx, sport, cfg2, markets, participants.get(sport, {}), names, now, stats,
                                  extra_books=[b for b in books if b not in refused])
            if ev:
                events.append(ev)
    print(f"Requests used this run: {client.count}")
    return events, [b for b in books if b not in refused]


def sharp_agreement(events, books, devig):
    """For each candidate book: how many selections it prices in full, and how far its no-vig probability sits from
    the main sharp book's (in percentage points)."""
    out = {b: {"priced": 0, "total": 0, "diffs": []} for b in books}
    for ev in events:
        for mkt in ev["markets"]:
            outs = mkt["outcomes"]
            main = devig([o["sharp"] for o in outs])
            for b in books:
                out[b]["total"] += len(outs)
                prices = [(o.get("others") or {}).get(b) for o in outs]
                if all(isinstance(x, (int, float)) and x > 1.0 for x in prices):
                    out[b]["priced"] += len(outs)
                    out[b]["diffs"] += [abs(a - c) * 100 for a, c in zip(main, devig(prices))]
    return out


def cmd_check_sharp(now, cfg, client, book_slug_list, sport, devig):
    """Compares candidate sharp books with the main one (first group of leagues only, 1 + one request per book)."""
    events, used = compare_books_run(now, cfg, client, book_slug_list, sport, max_groups=1)
    res = sharp_agreement(events, used, devig)
    print(f"\nHow each book's probabilities compare with {cfg['sharp_label']} ({sport}, first group of leagues):")
    for b in used:
        r = res[b]
        cov = (100 * r["priced"] // r["total"]) if r["total"] else 0
        if not r["diffs"]:
            print(f"  {b}: no complete markets priced. Not usable here.")
            continue
        mean = sum(r["diffs"]) / len(r["diffs"])
        worst = max(r["diffs"])
        if cov < 50:
            verdict = "too patchy to rely on"
        elif mean < 0.3:
            verdict = "almost a copy of the main book, so it adds little"
        elif mean <= 2.0:
            verdict = "a useful second opinion"
        else:
            verdict = "differs a lot: probably not as sharp, or defines markets differently"
        print(f"  {b}: prices {cov}% of selections, average gap {mean:.2f} points, largest {worst:.1f} points: {verdict}")
    print("(The verdict thresholds are rules of thumb. To use a book, add its name to sharp_extra_books in config.json.)")


def write_compare_page(rows, books, out_path, sharp_label):
    # keep selections that at least two of the books have a price for, so there is something to compare
    keep = [r for r in rows if sum(1 for b in books if (r.get("others") or {}).get(b)) >= min(2, len(books))]
    data = {"generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "sharp_label": sharp_label,
            "books": books, "rows": keep}
    payload = json.dumps(data, ensure_ascii=False).replace("<", "\\u003c")
    Path(out_path).write_text(COMPARE_TEMPLATE.replace("__DATA_JSON__", payload), encoding="utf-8")
    print(f"\nPrice coverage by book (share of {len(rows)} selections that have a price):")
    for b in books:
        have = sum(1 for r in rows if (r.get("others") or {}).get(b))
        print(f"  {b}: {have} ({(100 * have // len(rows)) if rows else 0}%)")
    return len(keep)


# --------------------------------------------------------------------------
# Settling logged bets: closing line value and results (run on your computer)
# --------------------------------------------------------------------------
RESULT_MAP = {"WIN": "won", "LOSE": "lost", "PUSH": "push", "CANCELLED": "push", "HALFWIN": "halfwon", "HALFLOSS": "halflost"}
HISTORICAL_GAP = 5.2          # OddsPapi asks for 5 seconds between historical-odds calls
MAX_SETTLE_REQUESTS = 30


def _latest_active_before(snapshots, start):
    """The latest active price recorded at or before kickoff, as (time, price), or None."""
    best = None
    for snap in snapshots or []:
        try:
            t = _parse_time(snap.get("createdAt"))
        except (ValueError, TypeError, AttributeError):
            continue
        price = snap.get("price")
        if t <= start and snap.get("active") is not False and isinstance(price, (int, float)) and price > 1.0:
            if best is None or t > best[0]:
                best = (t, float(price))
    return best


def closing_probabilities(hist, market_id, outcome_ids, start, devig, books, main_slug, weights=None):
    """No-vig closing probability for every outcome of one market, averaged over the sharp books that have a
    closing price for all of its outcomes (the main book counts 2, others 1, unless `weights` says otherwise).
    Returns (probabilities in the order of outcome_ids, minutes between the last update and kickoff, books used)
    or None when the main book has no complete closing set."""
    weights = weights or {}
    per_book, last_update = [], None
    for slug in books:
        outs = (((hist.get("bookmakers") or {}).get(slug) or {}).get("markets") or {}).get(str(market_id), {}).get("outcomes") or {}
        found = []
        for oid in outcome_ids:
            snaps = (((outs.get(str(oid)) or {}).get("players")) or {}).get("0")
            found.append(_latest_active_before(snaps, start))
        if any(f is None for f in found):
            continue
        w = weights.get(slug)
        w = float(w) if isinstance(w, (int, float)) and w > 0 else (2.0 if slug == main_slug else 1.0)
        per_book.append((slug, devig([price for _, price in found]), w))
        newest = max(t for t, _ in found)
        last_update = newest if last_update is None or newest > last_update else last_update
    if not per_book or per_book[0][0] != main_slug:
        return None
    total = sum(w for _, _, w in per_book)
    probs = [sum(pb[i] * w for _, pb, w in per_book) / total for i in range(len(outcome_ids))]
    minutes = round((start - last_update).total_seconds() / 60) if last_update else None
    return probs, minutes, [slug for slug, _, _ in per_book]


def cmd_settle_bets(client, cfg, path, out_path, now):
    """Reads bets exported from the page, fetches closing prices (CLV) and results from OddsPapi, and writes the
    bets back with those filled in. About 2 requests per game you bet on."""
    raw = json.loads(Path(path).read_text(encoding="utf-8"))
    bets = raw.get("bets") if isinstance(raw, dict) else raw
    if not isinstance(bets, list):
        raise SystemExit("That file doesn't look like exported bets. Use the Copy bets button on the page and save the text.")
    markets = _load_cache(MARKETS_CACHE_PATH, "market definitions", "--build-markets").get("markets", {})
    sharp = cfg["sharp_book"]
    books = ([sharp] + [b for b in (cfg.get("sharp_extra_books") or []) if b and b != sharp])[:3]

    work, skipped = {}, 0
    for b in bets:
        try:
            start = _parse_time(b["start"])
        except (KeyError, ValueError, TypeError):
            skipped += 1
            continue
        if not (b.get("fixture_id") and b.get("market_id") and b.get("outcome_id")):
            skipped += 1
            continue
        needs_clv = b.get("clv_pct") is None and start <= now
        needs_result = b.get("result") in (None, "", "pending") and now - start >= timedelta(hours=3)
        if needs_clv or needs_result:
            entry = work.setdefault(b["fixture_id"], {"bets": [], "clv": False, "result": False})
            entry["bets"].append(b)
            entry["clv"] = entry["clv"] or needs_clv
            entry["result"] = entry["result"] or needs_result
    needed = sum(int(e["clv"]) + int(e["result"]) for e in work.values())
    print(f"{len(bets)} bets read. {len(work)} games need closing prices or results: {needed} requests"
          + (f" ({skipped} bets skipped: logged by an older page version or missing a start time)." if skipped else "."))
    if not work:
        print("Nothing to do yet. Games must have started (and results need about 3 hours after kickoff).")
        Path(out_path).write_text(json.dumps(bets, indent=2), encoding="utf-8")
        return
    if needed > MAX_SETTLE_REQUESTS:
        raise SystemExit(f"That would use {needed} requests. Settle in smaller batches (at most {MAX_SETTLE_REQUESTS} at a time).")
    try:
        sub = get_subscription(client)
        limit, used = sub.get("request_limit"), sub.get("request_count")
        if isinstance(limit, (int, float)) and isinstance(used, (int, float)) and limit - used < needed:
            raise SystemExit(f"Only {int(limit - used)} requests left on your plan and this needs {needed}. Stopping.")
    except ApiError:
        pass
    client.max_requests = max(client.max_requests, needed)

    report = []
    for fid, entry in work.items():
        hist = sett = None
        try:
            if entry["clv"]:
                hist = client.get("/v4/historical-odds", {"fixtureId": fid, "bookmakers": ",".join(books)}, gap=HISTORICAL_GAP)
            if entry["result"]:
                sett = client.get("/v4/settlements", {"fixtureId": fid})
        except ApiError as e:
            if "HTTP 404" in str(e) or "NOT_FOUND" in str(e):
                print(f"  {fid}: no data available yet, skipped.")
                continue
            raise
        for b in entry["bets"]:
            start = _parse_time(b["start"])
            row = {"event": b.get("event"), "selection": b.get("selection"), "taken": b.get("taken_odds")}
            m = markets.get(str(b["market_id"]))
            if hist is not None and m is not None and b.get("clv_pct") is None:
                ids = [o["id"] for o in m["outcomes"]]
                got = closing_probabilities(hist, b["market_id"], ids, start, DEVIG_FUNCS[cfg.get("devig", "power")],
                                            books, sharp, cfg.get("sharp_weights"))
                if got and b["outcome_id"] in ids:
                    probs, minutes, used_books = got
                    p_close = probs[ids.index(b["outcome_id"])]
                    b["closing_p"] = round(p_close, 5)
                    b["closing_fair"] = round(1.0 / p_close, 3)
                    b["clv_pct"] = round(float(b["taken_odds"]) * p_close - 1.0, 5)
                    b["closing_books"] = used_books
                    b["closing_minutes_before_kickoff"] = minutes
            if sett is not None and b.get("result") in (None, "", "pending"):
                res = ((((sett.get("markets") or {}).get(str(b["market_id"])) or {}).get("outcomes") or {})
                       .get(str(b["outcome_id"])) or {}).get("players", {}).get("0", {}).get("result")
                if res in RESULT_MAP:
                    b["result"] = RESULT_MAP[res]
                    b["settled_by"] = "OddsPapi"
            row["closing_fair"], row["clv"], row["result"] = b.get("closing_fair"), b.get("clv_pct"), b.get("result")
            report.append(row)
    Path(out_path).write_text(json.dumps(bets, indent=2), encoding="utf-8")
    print("\nEvent | selection | you took | closing fair odds | CLV | result")
    for r in report:
        clv = f"{r['clv'] * 100:+.1f}%" if r["clv"] is not None else "n/a"
        print(f"  {r['event']} | {r['selection']} | {r['taken']} | {r['closing_fair'] or 'n/a'} | {clv} | {r['result'] or 'pending'}")
    with_clv = [r["clv"] for r in report if r["clv"] is not None]
    if with_clv:
        print(f"\nAverage CLV on {len(with_clv)} bets: {sum(with_clv) / len(with_clv) * 100:+.1f}%. "
              "Positive means you usually got a better price than the sharp closing price.")
    print(f"Wrote {out_path}. Import it with the page's Import button. Requests used this run: {client.count}")


# --------------------------------------------------------------------------
# Optional password lock (for publishing on a public link)
# --------------------------------------------------------------------------
LOCK_ITERATIONS = 600_000      # PBKDF2-SHA256 rounds; a phone does this in about a second

LOCK_TEMPLATE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="color-scheme" content="light dark">
<meta name="robots" content="noindex,nofollow">
<title>Edge scanner</title>
<style>
  :root { --chalk:#EEF2F1; --paper:#FFFFFF; --ink:#14262B; --slate:#566A6F; --rule:#D3DDDC; --accent:#2D3FE0; --brick:#B3402F; }
  @media (prefers-color-scheme: dark) {
    :root { --chalk:#0E1A1D; --paper:#15262A; --ink:#E6EEEE; --slate:#9BAFB3; --rule:#2A3D41; --accent:#9AA8FF; --brick:#F29A8A; }
  }
  * { box-sizing: border-box; }
  body { margin:0; min-height:100vh; display:flex; align-items:center; justify-content:center; padding:20px;
         background:var(--chalk); color:var(--ink);
         font-family: system-ui, -apple-system, "Segoe UI", Roboto, Helvetica, Arial, sans-serif; font-size:16px; line-height:1.45; }
  main { width:100%; max-width:380px; }
  h1 { font-size:1.5rem; margin:0 0 6px; }
  p { margin:0 0 14px; color:var(--slate); }
  p.err { color:var(--brick); font-weight:500; }
  label { display:block; font-size:.85rem; color:var(--slate); margin-bottom:4px; }
  input[type=password] { width:100%; min-height:48px; padding:8px 12px; font:inherit; font-size:1rem; color:var(--ink);
                         background:var(--paper); border:1px solid var(--rule); border-radius:8px; }
  .remember { display:flex; align-items:center; gap:8px; margin:12px 0; font-size:.95rem; color:var(--ink); }
  .remember input { width:20px; height:20px; }
  button { width:100%; min-height:48px; font:inherit; font-weight:700; border:0; border-radius:8px; background:var(--ink); color:var(--chalk); cursor:pointer; }
  button:disabled { opacity:.6; cursor:default; }
  :focus-visible { outline:2px solid var(--accent); outline-offset:2px; }
</style>
</head>
<body>
<main>
  <h1>Edge scanner</h1>
  <p id="msg">Enter the password to open the page.</p>
  <form id="f">
    <label for="pw">Password</label>
    <input id="pw" type="password" autocomplete="current-password" required>
    <label class="remember"><input id="rem" type="checkbox" checked> Remember on this device</label>
    <button id="go" type="submit">Open</button>
  </form>
</main>
<script>
(function () {
  "use strict";
  var P = __PAYLOAD__;
  var KEY = "edge-scanner-pw";
  var msg = document.getElementById("msg"), form = document.getElementById("f");
  var pw = document.getElementById("pw"), rem = document.getElementById("rem"), go = document.getElementById("go");

  function b64(s) {
    var bin = atob(s), a = new Uint8Array(bin.length);
    for (var i = 0; i < bin.length; i++) a[i] = bin.charCodeAt(i);
    return a;
  }
  async function decrypt(password) {
    var base = await crypto.subtle.importKey("raw", new TextEncoder().encode(password), "PBKDF2", false, ["deriveKey"]);
    var key = await crypto.subtle.deriveKey(
      { name: "PBKDF2", salt: b64(P.salt), iterations: P.iter, hash: "SHA-256" },
      base, { name: "AES-GCM", length: 256 }, false, ["decrypt"]);
    var plain = await crypto.subtle.decrypt({ name: "AES-GCM", iv: b64(P.iv) }, key, b64(P.data));
    return new TextDecoder().decode(plain);
  }
  function show(text, isError) { msg.textContent = text; msg.className = isError ? "err" : ""; }
  async function attempt(password, remember) {
    if (!(window.crypto && crypto.subtle)) { show("This page needs a secure (https) connection.", true); return; }
    go.disabled = true; show("Opening...", false);
    try {
      var html = await decrypt(password);
      try { if (remember) localStorage.setItem(KEY, password); } catch (e) { /* storage unavailable */ }
      document.open(); document.write(html); document.close();
    } catch (e) {
      try { localStorage.removeItem(KEY); } catch (e2) { /* ignore */ }
      go.disabled = false;
      show("That password didn't work. Try again.", true);
    }
  }
  form.addEventListener("submit", function (ev) { ev.preventDefault(); attempt(pw.value, rem.checked); });
  var saved = null;
  try { saved = localStorage.getItem(KEY); } catch (e) { /* ignore */ }
  if (saved) attempt(saved, true);
})();
</script>
</body>
</html>
"""


def lock_page(html_text, password):
    """Encrypt the finished page (AES-256-GCM, key from the password with PBKDF2). The result is a small page that
    asks for the password in the browser and decrypts it there. The data is never readable without the password."""
    if len(password) < 10:
        raise SystemExit("PAGE_PASSWORD is too short. Use at least 10 characters (a few random words is ideal): "
                         "the encrypted page is public, so a short password could be guessed offline.")
    try:
        from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    except ImportError:
        raise SystemExit("Locking the page needs the 'cryptography' package:  pip install cryptography")
    salt, iv = os.urandom(16), os.urandom(12)
    key = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, LOCK_ITERATIONS, dklen=32)
    ciphertext = AESGCM(key).encrypt(iv, html_text.encode("utf-8"), None)      # ciphertext + tag, as WebCrypto expects
    payload = {"salt": base64.b64encode(salt).decode(), "iv": base64.b64encode(iv).decode(),
               "data": base64.b64encode(ciphertext).decode(), "iter": LOCK_ITERATIONS}
    return LOCK_TEMPLATE.replace("__PAYLOAD__", json.dumps(payload))


# --------------------------------------------------------------------------
# Self-test (no internet needed)
# --------------------------------------------------------------------------
def _fake_book(prices, **extra):
    """prices: {marketId: [(outcomeId, price, mainLine), ...]} -> a bookmaker block shaped like the v4 docs."""
    block = {"bookmakerIsActive": True, "suspended": False, "markets": {}}
    block.update(extra)
    for mid, outs in prices.items():
        block["markets"][str(mid)] = {
            "marketActive": True,
            "outcomes": {str(oid): {"players": {"0": {"active": True, "price": price, "mainLine": main}}}
                         for oid, price, main in outs},
        }
    return block


def run_tests():
    # --- math ---
    for name, fn in DEVIG_FUNCS.items():
        for odds in ([1.91, 1.95], [2.10, 3.45, 3.60], [1.20, 5.00], [1.55, 2.45]):
            probs = fn(odds)
            assert abs(sum(probs) - 1.0) < 1e-9, (name, odds, probs)
            assert all(0 < x < 1 for x in probs), (name, odds, probs)
    assert abs(min_odds(0.55, 0.03) - 1.8727) < 1e-3
    assert all(abs(x - 0.5) < 1e-9 for x in devig_proportional([1.92307692, 1.92307692]))
    assert devig_power([1.20, 5.00])[1] < devig_proportional([1.20, 5.00])[1]

    # --- live parsing, using a made-up fixture shaped like the documented v4 response ---
    now = datetime.now(timezone.utc)
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    cfg["compare_book"] = "bet365"
    markets = {
        "111": {"sport": "Basketball", "type": "moneyline", "period": "result", "handicap": 0,
                "outcomes": [{"id": 111, "name": "1"}, {"id": 112, "name": "2"}]},
        "11120": {"sport": "Basketball", "type": "totals", "period": "result", "handicap": 224.5,
                  "outcomes": [{"id": 11120, "name": "Over"}, {"id": 11121, "name": "Under"}]},
        "11122": {"sport": "Basketball", "type": "totals", "period": "result", "handicap": 230.5,
                  "outcomes": [{"id": 11122, "name": "Over"}, {"id": 11123, "name": "Under"}]},
        "11130": {"sport": "Basketball", "type": "totals", "period": "p1", "handicap": 110.5,
                  "outcomes": [{"id": 11130, "name": "Over"}, {"id": 11131, "name": "Under"}]},
    }
    names = {"3409": "Metro Surge", "3410": "Coastline Waves"}
    tnames = {132: "NBA"}

    def fixture(sharp=None, bet=None, status=0, hours=3, p2=3410):
        sharp_prices = {111: [(111, 1.55, True), (112, 2.45, True)],
                        11120: [(11120, 1.90, True), (11121, 1.96, True)],
                        11122: [(11122, 2.40, False), (11123, 1.55, False)],     # not the main line
                        11130: [(11130, 1.90, True), (11131, 1.90, True)]}       # first half: ignored
        bet_prices = {111: [(111, 1.53, True), (112, 2.60, True)],
                      11120: [(11120, 2.05, True), (11121, 1.85, True)]}
        return {
            "fixtureId": "id1100013200000001", "participant1Id": 3409, "participant2Id": p2, "sportId": 11,
            "tournamentId": 132, "statusId": status, "hasOdds": True,
            "startTime": (now + timedelta(hours=hours)).strftime("%Y-%m-%dT%H:%M:%S.000Z"),
            "bookmakerOdds": {"pinnacle": sharp or _fake_book(sharp_prices), "bet365": bet or _fake_book(bet_prices)},
        }

    st = Counter()
    ev = fixture_to_event(fixture(), "Basketball", cfg, markets, names, tnames, now, st)
    assert ev and ev["event"] == "Metro Surge vs Coastline Waves" and ev["league"] == "NBA", ev
    assert [m["market"] for m in ev["markets"]] == ["Moneyline", "Total 224.5"], [m["market"] for m in ev["markets"]]
    ml = ev["markets"][0]["outcomes"]
    assert [o["name"] for o in ml] == ["Metro Surge", "Coastline Waves"]
    assert ml[0]["sharp"] == 1.55 and ml[1]["bet365"] == 2.60
    assert [o["name"] for o in ev["markets"][1]["outcomes"]] == ["Over 224.5", "Under 224.5"]
    assert st["skipped market: not the main line"] == 1
    assert st["skipped market: period 'p1' not enabled"] == 1

    # sharp book suspended, game already started, unknown team, no Bet365 block
    assert fixture_to_event(fixture(sharp=_fake_book({111: [(111, 1.5, True), (112, 2.5, True)]}, suspended=True)),
                            "Basketball", cfg, markets, names, tnames, now, Counter()) is None
    assert fixture_to_event(fixture(hours=-1), "Basketball", cfg, markets, names, tnames, now, Counter()) is None
    st3 = Counter()
    ev3 = fixture_to_event(fixture(p2=999), "Basketball", cfg, markets, names, tnames, now, st3)
    assert ev3["event"] == "Metro Surge vs Team 999" and st3["team names missing (run --build-participants)"] == 1
    fx4 = fixture()
    del fx4["bookmakerOdds"]["bet365"]
    ev4 = fixture_to_event(fx4, "Basketball", cfg, markets, names, tnames, now, Counter())
    assert all(o["bet365"] is None for m in ev4["markets"] for o in m["outcomes"])
    cfg_no_compare = dict(cfg, compare_book=None)             # the default: sharp book only
    ev5 = fixture_to_event(fixture(), "Basketball", cfg_no_compare, markets, names, tnames, now, Counter())
    assert ev5 and all(o["bet365"] is None for m in ev5["markets"] for o in m["outcomes"])

    # --- both teams to score, spreads, and the spread sign check ---
    markets2 = dict(markets)
    markets2["200"] = {"sport": "Soccer", "name": "Both Teams To Score", "type": "btts", "period": "fulltime", "handicap": 0,
                       "outcomes": [{"id": 200, "name": "Yes"}, {"id": 201, "name": "No"}]}
    markets2["300"] = {"sport": "Basketball", "name": "Spread", "type": "spreads", "period": "result", "handicap": -3.5,
                       "outcomes": [{"id": 300, "name": "1"}, {"id": 301, "name": "2"}]}
    cfg2 = dict(cfg, market_types=["moneyline", "1x2", "totals", "spreads", "btts"])
    fx6 = fixture()
    fx6["bookmakerOdds"]["pinnacle"] = _fake_book({111: [(111, 1.55, True), (112, 2.45, True)],
                                                   300: [(300, 1.91, True), (301, 1.95, True)],
                                                   200: [(200, 1.80, True), (201, 2.00, True)]})
    st6 = Counter()
    ev6 = fixture_to_event(fx6, "Soccer", cfg2, markets2, names, tnames, now, st6)
    assert [m["market"] for m in ev6["markets"]] == ["Moneyline", "Spread -3.5 (first-listed team)", "Both teams to score"]
    assert [o["name"] for o in ev6["markets"][1]["outcomes"]] == ["Metro Surge -3.5", "Coastline Waves +3.5"]
    assert [o["name"] for o in ev6["markets"][2]["outcomes"]] == ["BTTS Yes", "BTTS No"]
    assert st6["spread sign check: matches the favorite"] == 1 and not st6["spread sign check: does NOT match the favorite"]
    markets3 = dict(markets2, **{"300": dict(markets2["300"], handicap=3.5)})   # a reversed convention would look like this
    st7 = Counter()
    fixture_to_event(fx6, "Soccer", cfg2, markets3, names, tnames, now, st7)
    assert st7["spread sign check: does NOT match the favorite"] == 1
    # spreads and BTTS stay out unless enabled in config.json
    cfg_basic = dict(cfg, market_types=["moneyline", "1x2", "totals"])
    ev8 = fixture_to_event(fx6, "Soccer", cfg_basic, markets2, names, tnames, now, Counter())
    assert [m["market"] for m in ev8["markets"]] == ["Moneyline"]

    # --- OddsPapi's real marketType names (taken from --find-markets output) ---
    ou = [{"outcomeName": "Under"}, {"outcomeName": "Over"}]
    yn = [{"outcomeName": "No"}, {"outcomeName": "Yes"}]
    assert classify_market({"marketType": "bothteamsscore", "outcomes": yn}, "Soccer") == "btts"
    assert classify_market({"marketType": "bothteamsscore", "outcomes": yn}, "Hockey") is None
    assert classify_market({"marketType": "totals-corners", "outcomes": ou}, "Soccer") == "corners_totals"
    assert classify_market({"marketType": "totals", "outcomes": ou}, "Basketball") == "totals"
    assert classify_market({"marketType": "totals", "outcomes": yn}, "Soccer") is None
    assert classify_market({"marketType": "teamtotals-team1", "outcomes": ou}, "Soccer") is None
    assert classify_market({"marketType": "spreads-european", "outcomes": []}, "Soccer") is None
    assert classify_market({"marketType": "1x2-corners", "outcomes": [{"outcomeName": o} for o in "2 1 X".split()]}, "Soccer") == "corners_1x2"
    assert classify_market({"marketType": "moneyline", "outcomes": []}, "Baseball") == "moneyline"

    corners = {"sport": "Soccer", "name": "Corners", "type": "corners_totals", "period": "fulltime", "handicap": 9.5,
               "outcomes": [{"id": 900, "name": "Under"}, {"id": 901, "name": "Over"}]}
    assert market_label(corners, "Soccer") == "Corners total 9.5"
    assert outcome_label(corners, "Over", "A", "B") == "Corners Over 9.5"
    assert market_label(dict(corners, handicap=9.25), "Soccer") == "Corners total 9.25 (quarter line)"
    assert market_label({"type": "totals", "handicap": 2.5}, "Soccer") == "Total 2.5"
    assert market_label({"type": "totals", "handicap": 2.75}, "Soccer") == "Total 2.75 (quarter line)"
    markets4 = dict(markets, **{"900": corners})
    cfg4 = dict(cfg, market_types=["moneyline", "corners_totals"])
    fx9 = fixture()
    fx9["bookmakerOdds"]["pinnacle"] = _fake_book({111: [(111, 1.55, True), (112, 2.45, True)],
                                                   900: [(900, 1.95, True), (901, 1.95, True)]})
    ev9 = fixture_to_event(fx9, "Soccer", cfg4, markets4, names, tnames, now, Counter())
    assert [m["market"] for m in ev9["markets"]] == ["Moneyline", "Corners total 9.5"]
    assert [o["name"] for o in ev9["markets"][1]["outcomes"]] == ["Corners Under 9.5", "Corners Over 9.5"]

    rows = build_rows([ev], devig_power)
    assert len(rows) == 4 and all(0 < r["p"] < 1 for r in rows)
    # --- other books' prices are carried alongside the sharp price (used by --compare-books) ---
    fx10 = fixture()
    fx10["bookmakerOdds"]["betano.mx"] = _fake_book({111: [(111, 1.50, True), (112, 2.50, True)]})
    ev10 = fixture_to_event(fx10, "Basketball", cfg, markets, names, tnames, now, Counter(),
                            extra_books=["betano.mx", "codere.es"])
    ml10 = ev10["markets"][0]["outcomes"]
    assert ml10[0]["others"] == {"betano.mx": 1.50, "codere.es": None}, ml10[0]
    assert ml10[1]["others"]["betano.mx"] == 2.50
    assert "others" not in fixture_to_event(fixture(), "Basketball", cfg, markets, names, tnames, now, Counter())["markets"][0]["outcomes"][0]
    assert build_rows([ev10], devig_power)[0]["others"]["betano.mx"] == 1.50

    # --- per-sport comparison settings (and the older single-setting form) ---
    by, dflt = compare_settings({"compare_book": "betano.mx",
                                 "compare_by_sport": {"Soccer": {"factor": 1.02, "spread_pct": 3.0}},
                                 "compare_default": {"factor": 1.0, "spread_pct": 5.0}})
    assert by == {"Soccer": {"factor": 1.02, "spread": 0.03}} and dflt == {"factor": 1.0, "spread": 0.05}
    by2, dflt2 = compare_settings({"compare_book": "betano.mx", "compare_factor": 1.0, "compare_spread_pct": 3.0,
                                   "compare_sports": ["Soccer"]})
    assert by2 == {"Soccer": {"factor": 1.0, "spread": 0.03}} and dflt2 is None
    by3, _ = compare_settings({"compare_book": "bet365"})
    assert set(by3) == set(SPORTS) and by3["Hockey"]["spread"] == 0.0
    ci = compare_info({"compare_book": "betano.mx", "compare_by_sport": {"Soccer": {"spread_pct": 3.0}},
                       "compare_default": {"spread_pct": 5.0}, "compare_label": "Betano MX", "your_book_label": "Playdoit"})
    assert ci["by_sport"]["Soccer"]["spread"] == 0.03 and ci["default"]["spread"] == 0.05 and ci["your_book"] == "Playdoit"
    assert compare_info({"compare_book": None}) is None

    # --- consensus probability across several sharp books ---
    base_ev = {"sport": "Basketball", "league": "NBA", "event": "A vs B", "start": now + timedelta(hours=3), "markets": [
        {"market": "Moneyline", "outcomes": [
            {"name": "A", "sharp": 1.80, "bet365": None, "others": {"singbet": 1.85, "sbobet": None}},
            {"name": "B", "sharp": 2.10, "bet365": None, "others": {"singbet": 2.02, "sbobet": None}}]}]}
    r_one = build_rows([base_ev], devig_power)
    assert all(r["n_books"] == 1 and r["p_range"] == 0 and r["p"] == r["p_main"] for r in r_one)
    assert "others" in r_one[0]                                    # kept when it isn't being used as a sharp book
    r_two = build_rows([base_ev], devig_power, sharp_extra=["singbet", "sbobet"], main_slug="pinnacle")
    assert all(r["n_books"] == 2 for r in r_two)                   # sbobet has no prices, so it is ignored
    assert abs(sum(r["p"] for r in r_two) - 1.0) < 1e-3
    pa_main, pa_sing = devig_power([1.80, 2.10])[0], devig_power([1.85, 2.02])[0]
    assert abs(r_two[0]["p"] - (2 * pa_main + pa_sing) / 3) < 1e-4  # main book weighs 2, the extra 1
    assert abs(r_two[0]["p_range"] - abs(pa_main - pa_sing)) < 1e-4
    assert "others" not in r_two[0] or "singbet" not in r_two[0]["others"]   # raw extra-book prices aren't published
    r_w = build_rows([base_ev], devig_power, sharp_extra=["singbet"], weights={"pinnacle": 1, "singbet": 1})
    assert abs(r_w[0]["p"] - (pa_main + pa_sing) / 2) < 1e-4

    # --- agreement statistics for candidate sharp books ---
    ag = sharp_agreement([base_ev], ["singbet", "sbobet"], devig_power)
    assert ag["singbet"]["priced"] == 2 and len(ag["singbet"]["diffs"]) == 2 and ag["singbet"]["diffs"][0] > 0
    assert ag["sbobet"]["priced"] == 0 and ag["sbobet"]["total"] == 2

    # --- closing prices and results for settled bets ---
    ko = datetime(2026, 5, 1, 18, 0, tzinfo=timezone.utc)

    def snap(minutes_from_ko, price, active=True):
        return {"createdAt": (ko + timedelta(minutes=minutes_from_ko)).isoformat(), "price": price, "active": active}

    def book_block(prices):
        return {"markets": {"101": {"outcomes": {str(oid): {"players": {"0": snaps}} for oid, snaps in prices.items()}}}}

    pin = book_block({101: [snap(-120, 2.20), snap(-10, 2.10), snap(1, 9.0, active=False), snap(5, 1.5)],
                      102: [snap(-60, 3.45)], 103: [snap(-30, 3.70), snap(-8, 3.60)]})
    assert _latest_active_before(pin["markets"]["101"]["outcomes"]["101"]["players"]["0"], ko) == (ko - timedelta(minutes=10), 2.10)
    assert _latest_active_before([], ko) is None and _latest_active_before([snap(5, 2.0)], ko) is None
    want = devig_power([2.10, 3.45, 3.60])
    got = closing_probabilities({"bookmakers": {"pinnacle": pin}}, 101, [101, 102, 103], ko, devig_power, ["pinnacle"], "pinnacle")
    assert got and all(abs(a - b) < 1e-12 for a, b in zip(got[0], want)) and got[1] == 8 and got[2] == ["pinnacle"], got
    sing_full = book_block({101: [snap(-5, 2.00)], 102: [snap(-5, 3.60)], 103: [snap(-5, 3.50)]})
    sing_part = book_block({101: [snap(-5, 2.00)], 102: [snap(-5, 3.60)]})
    both = closing_probabilities({"bookmakers": {"pinnacle": pin, "singbet": sing_full}}, 101, [101, 102, 103], ko, devig_power,
                                 ["pinnacle", "singbet"], "pinnacle")
    mix = [(2 * a + b) / 3 for a, b in zip(devig_power([2.10, 3.45, 3.60]), devig_power([2.00, 3.60, 3.50]))]
    assert both and all(abs(a - b) < 1e-12 for a, b in zip(both[0], mix)) and both[2] == ["pinnacle", "singbet"]
    only_main = closing_probabilities({"bookmakers": {"pinnacle": pin, "singbet": sing_part}}, 101, [101, 102, 103], ko, devig_power,
                                      ["pinnacle", "singbet"], "pinnacle")
    assert only_main[2] == ["pinnacle"]                     # a book with an incomplete set is left out
    assert closing_probabilities({"bookmakers": {"singbet": sing_full}}, 101, [101, 102, 103], ko, devig_power,
                                 ["pinnacle", "singbet"], "pinnacle") is None   # no main-book close: no CLV

    # --- pasted keys are cleaned up ---
    assert _clean_key('  "11111111-2222-3333-4444-555555555555"\n') == "11111111-2222-3333-4444-555555555555"
    assert _clean_key("'abc'") == "abc" and _clean_key("   ") is None and _clean_key(None) is None

    # --- password lock round trip (needs the optional 'cryptography' package) ---
    try:
        from cryptography.hazmat.primitives.ciphers.aead import AESGCM
        locked = lock_page("<html>secret picks</html>", "correct horse battery")
        assert "secret picks" not in locked and "correct horse" not in locked
        pl = json.loads(locked.split("var P = ", 1)[1].split(";\n  var KEY", 1)[0])
        k = hashlib.pbkdf2_hmac("sha256", b"correct horse battery", base64.b64decode(pl["salt"]), pl["iter"], dklen=32)
        assert AESGCM(k).decrypt(base64.b64decode(pl["iv"]), base64.b64decode(pl["data"]), None) == b"<html>secret picks</html>"
        try:
            lock_page("x", "short")
            raise AssertionError("a short password must be refused")
        except SystemExit:
            pass
    except ImportError:
        print("(skipped the password-lock check: 'cryptography' isn't installed)")
    print("All checks passed.")


# --------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Build the edge scanner page.")
    ap.add_argument("--live", action="store_true", help="use real odds from OddsPapi")
    ap.add_argument("--check", action="store_true", help="test your API key and see your plan (free)")
    ap.add_argument("--diagnose", action="store_true", help="probe OddsPapi's answers to find connection problems (free)")
    ap.add_argument("--find-tournaments", action="store_true", help="list tournament IDs to put in config.json")
    ap.add_argument("--compare-books", nargs="?", const="default", metavar="BOOKS",
                    help='compare other books with yours: writes book_compare.html (uses 1 + one request per book; '
                         'Soccer unless --sport is given). Example: --compare-books "betano.mx,betcris"')
    ap.add_argument("--check-sharp", nargs="?", const="default", metavar="BOOKS",
                    help='test other sharp books against the main one (1 + one request per book; Soccer unless --sport). '
                         'Example: --check-sharp "singbet,sbobet,betfair-ex"')
    ap.add_argument("--settle-bets", metavar="FILE",
                    help="fetch closing prices (CLV) and results for bets exported from the page; "
                         "writes bets_settled.json (about 2 requests per game)")
    ap.add_argument("--find-bookmakers", metavar="TEXT", help='look up bookmaker names, e.g. "playdoit,caliente" (1 request)')
    ap.add_argument("--find-markets", metavar="TEXT", help='look up market names, e.g. "corner,both teams" (1 request)')
    ap.add_argument("--build-markets", action="store_true", help="save market definitions to markets_cache.json")
    ap.add_argument("--build-participants", action="store_true", help="save team names to participants_cache.json")
    ap.add_argument("--sport", choices=SPORTS, help="limit --find-tournaments / --find-markets / --build-participants / --compare-books / --check-sharp to one sport")
    ap.add_argument("--search", default="", help="with --find-tournaments: only show names containing this text")
    ap.add_argument("--devig", choices=sorted(DEVIG_FUNCS), default="power",
                    help="how to remove the margin (default: power)")
    ap.add_argument("--out", default="index.html", help="output file (default: index.html)")
    ap.add_argument("--lock", action="store_true",
                    help="password-protect the page using the PAGE_PASSWORD environment variable")
    ap.add_argument("--test", action="store_true", help="run the checks and exit")
    args = ap.parse_args()

    if args.test:
        run_tests()
        return 0

    cfg = load_config()
    now = datetime.now(timezone.utc)
    if args.diagnose:
        cmd_diagnose(cfg)
        return 0
    try:
        if (args.check or args.find_tournaments or args.find_markets or args.find_bookmakers
                or args.build_markets or args.build_participants):
            client = make_client(cfg)
            if args.check:
                cmd_check(client, cfg)
            if args.find_tournaments:
                cmd_find_tournaments(client, cfg, args.sport, args.search)
            if args.find_bookmakers:
                cmd_find_bookmakers(client, cfg, args.find_bookmakers)
            if args.find_markets:
                cmd_find_markets(client, cfg, args.find_markets, args.sport)
            if args.build_markets:
                cmd_build_markets(client, cfg)
            if args.build_participants:
                cmd_build_participants(client, cfg, args.sport)
            return 0

        if args.check_sharp is not None:
            client = make_client(cfg)
            wanted = ["singbet", "sbobet", "betfair-ex"] if args.check_sharp == "default" else args.check_sharp.split(",")
            cmd_check_sharp(now, cfg, client, [w.strip() for w in wanted], args.sport or "Soccer", DEVIG_FUNCS[args.devig])
            return 0

        if args.settle_bets:
            client = make_client(cfg)
            out = args.out if args.out != "index.html" else "bets_settled.json"
            cmd_settle_bets(client, dict(cfg, devig=args.devig), args.settle_bets, out, now)
            return 0

        if args.compare_books is not None:
            client = make_client(cfg)
            wanted = cfg["calibration_books"] if args.compare_books == "default" else args.compare_books.split(",")
            sport = args.sport or "Soccer"
            events, used_books = compare_books_run(now, cfg, client, [w.strip() for w in wanted], sport)
            out = args.out if args.out != "index.html" else "book_compare.html"
            kept = write_compare_page(build_rows(events, DEVIG_FUNCS[args.devig]), used_books, out, cfg["sharp_label"])
            print(f"Wrote {out} with {kept} picks to compare. Open it on your computer.")
            return 0

        if args.live:
            client = make_client(cfg)
            events = live_events(now, cfg, client)
            source, label, compare = "live", cfg["sharp_label"], compare_info(cfg)
        else:
            events, source, label = sample_events(now), "sample", SHARP_BOOK
            compare = {"label": "Bet365", "your_book": "your book", "by_sport": {}, "default": {"factor": 1.0, "spread": 0.0}}
    except ApiError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1

    rows = build_rows(events, DEVIG_FUNCS[args.devig],
                      sharp_extra=(cfg.get("sharp_extra_books") or []) if source == "live" else [],
                      main_slug=cfg["sharp_book"], weights=cfg.get("sharp_weights"))
    password = None
    if args.lock:
        password = os.environ.get("PAGE_PASSWORD")
        if not password:
            raise SystemExit("--lock needs the PAGE_PASSWORD environment variable to be set.")
    write_page(rows, source, args.devig, args.out, label, password, compare)
    print(f"\nWrote {args.out}: {len(rows)} selections from {len(events)} events "
          f"({source} data, {DEVIG_LABELS[args.devig]}{', password-locked' if password else ''}).")
    if source == "live" and not rows:
        print("No usable selections. Check the 'What happened to the data' list above.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
