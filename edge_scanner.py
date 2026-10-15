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


def get_api_key():
    key = os.environ.get("ODDSPAPI_KEY") or _read_dotenv()
    if not key and sys.stdin.isatty():
        key = getpass.getpass("Paste your OddsPapi key (it won't be shown or saved): ")
    return key.strip() if key else None


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

    def get(self, path, params=None):
        billable = path != "/v4/account"
        query = {k: v for k, v in (params or {}).items() if v is not None}
        query["apiKey"] = self.key
        url = f"{self.base}{path}?{urllib.parse.urlencode(query)}"
        req = urllib.request.Request(url, headers={"Accept": "application/json", "User-Agent": "edge-scanner/1.0"})

        for attempt in range(3):
            if billable and self.count >= self.max_requests:
                raise ApiError(f"Stopped: reached max_requests_per_run ({self.max_requests}) in config.json.")
            pause = self.gap - (time.monotonic() - self._last)
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


def fixture_to_event(fx, sport, cfg, markets, names, tournament_names, now, stats):
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
            outcomes.append({
                "name": outcome_label(m, o["name"], p1, p2),
                "sharp": sm["outcomes"][o["id"]]["price"],
                "bet365": cq["price"] if cq else None,
            })
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
                            {"market": label, "outcomes": outcomes}))

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
    """OddsPapi v4 takes exactly one bookmaker per call, in the `bookmaker` parameter."""
    data = client.get("/v4/odds-by-tournaments", {
        "tournamentIds": ",".join(str(t["id"]) for t in tournaments),
        "bookmaker": slug,
    })
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

    needed = len(groups) * (2 if compare else 1)
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
    for label, tournaments in groups:
        fixtures = _fetch_book(client, tournaments, sharp)
        note = ""
        if compare_ok:
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
            ev = fixture_to_event(fx, sp, cfg, markets, participants.get(sp, {}), t_names, now, stats)
            if ev:
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
def build_rows(events, devig):
    rows = []
    for ev in events:
        for mkt in ev["markets"]:
            outcomes = mkt["outcomes"]
            probs = devig([o["sharp"] for o in outcomes])
            for o, p in zip(outcomes, probs):
                rows.append({
                    "id": f'{ev["event"]}|{mkt["market"]}|{o["name"]}',
                    "sport": ev["sport"],
                    "league": ev["league"],
                    "event": ev["event"],
                    "start": ev["start"].astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
                    "market": mkt["market"],
                    "selection": o["name"],
                    "sharp": o["sharp"],
                    "p": round(p, 5),
                    "fair": round(1.0 / p, 3),
                    "bet365": o.get("bet365"),
                })
    return rows


def write_page(rows, source, devig_name, out_path, sharp_label=SHARP_BOOK, password=None):
    now = datetime.now(timezone.utc)
    sports = list(SPORTS)   # the page greys out sports that have no games in this data
    data = {
        "generated_at": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "source": source,
        "sharp_book": sharp_label,
        "devig": DEVIG_LABELS[devig_name],
        "sports": sports,
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
    ap.add_argument("--find-tournaments", action="store_true", help="list tournament IDs to put in config.json")
    ap.add_argument("--find-markets", metavar="TEXT", help='look up market names, e.g. "corner,both teams" (1 request)')
    ap.add_argument("--build-markets", action="store_true", help="save market definitions to markets_cache.json")
    ap.add_argument("--build-participants", action="store_true", help="save team names to participants_cache.json")
    ap.add_argument("--sport", choices=SPORTS, help="limit --find-tournaments / --find-markets / --build-participants to one sport")
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
    try:
        if args.check or args.find_tournaments or args.find_markets or args.build_markets or args.build_participants:
            client = make_client(cfg)
            if args.check:
                cmd_check(client, cfg)
            if args.find_tournaments:
                cmd_find_tournaments(client, cfg, args.sport, args.search)
            if args.find_markets:
                cmd_find_markets(client, cfg, args.find_markets, args.sport)
            if args.build_markets:
                cmd_build_markets(client, cfg)
            if args.build_participants:
                cmd_build_participants(client, cfg, args.sport)
            return 0

        if args.live:
            client = make_client(cfg)
            events = live_events(now, cfg, client)
            source, label = "live", cfg["sharp_label"]
        else:
            events, source, label = sample_events(now), "sample", SHARP_BOOK
    except ApiError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1

    rows = build_rows(events, DEVIG_FUNCS[args.devig])
    password = None
    if args.lock:
        password = os.environ.get("PAGE_PASSWORD")
        if not password:
            raise SystemExit("--lock needs the PAGE_PASSWORD environment variable to be set.")
    write_page(rows, source, args.devig, args.out, label, password)
    print(f"\nWrote {args.out}: {len(rows)} selections from {len(events)} events "
          f"({source} data, {DEVIG_LABELS[args.devig]}{', password-locked' if password else ''}).")
    if source == "live" and not rows:
        print("No usable selections. Check the 'What happened to the data' list above.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
