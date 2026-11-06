#!/usr/bin/env python3
"""The Anthropic budget ledger (plan section 11, item 3).

`Ariadne/runs/budget.json` (git-ignored) holds what the pipeline spent on
Anthropic models since the last weekly reset, by role (prover,
annotator) and by model: calls, the four token counts, and the
API-equivalent cost in USD that Claude Code's JSON result reports
(`total_cost_usd`, `modelUsage.<model>.costUSD`).  Before each Claude call
the caller asks `reserve` with the call's per-goal cap; the call is
refused if the week's total would pass the cap.  After the call `charge`
books what it used.  Free models (GLM on REALLMS) are logged with
`log_free` and never charged.

**Unit: USD, not tokens.**  Raw token counts are dominated by cache
reads, which cost about a tenth of other input tokens, so the
API-equivalent cost tracks the usage limit better.  Tokens are kept too.

**Percent of the weekly limit** = cost x `pct_per_usd`, the calibration
factor stored in the ledger.  It is measured with `calibrate`: the
owner's weekly % from `/usage`, divided by the cost ccusage reports for
all Claude Code use on this machine since the weekly reset (which is what
the weekly limit counts, the owner's interactive sessions included).
Until then a conservative placeholder is used (PLACEHOLDER_PCT_PER_USD)
and every report says so.  The cap is 20% and the warning 15%; both are
of the weekly limit and apply to the ledger's own spending.

The week resets at `resets_at`: the totals move to `past_weeks` and the
next reset is a week later.  `resets_at` comes from `/usage` (read with
`claude -p /usage`, a local command with no model call) when it can be
read, else a week after the ledger was started.

    python3 budget.py show
    python3 budget.py usage            # read /usage (no tokens)
    python3 budget.py calibrate --percent P --since YYYY-MM-DD
"""
import argparse
import contextlib
import copy
import datetime as dt
import fcntl
import json
import os
import re
import subprocess
import uuid

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
PATH = os.path.join(ARIADNE, "runs", "budget.json")

CAP_PCT = 20.0
WARN_PCT = 15.0
# Not measured: 2% of the weekly limit per API-equivalent dollar puts the
# cap at $10, about 50 Sonnet goals at B1's size.  Deliberately high, so
# an uncalibrated ledger refuses early rather than late.
PLACEHOLDER_PCT_PER_USD = 2.0
WEEK = dt.timedelta(days=7)
# A reservation still pending after this long belongs to a run that
# died before charging; it stops counting against the cap.
PENDING_TTL = dt.timedelta(hours=6)
CCUSAGE = ["npx", "-y", "ccusage@20.0.40", "claude", "daily",
           "--breakdown", "--json"]
TOKEN_FIELDS = ("input_tokens", "output_tokens",
                "cache_creation_input_tokens", "cache_read_input_tokens")
# modelUsage's camelCase names for the same four.
MODEL_FIELDS = {"inputTokens": "input_tokens",
                "outputTokens": "output_tokens",
                "cacheCreationInputTokens": "cache_creation_input_tokens",
                "cacheReadInputTokens": "cache_read_input_tokens"}
ROLES = ("prover", "annotator")


def now_utc():
    return dt.datetime.now(dt.timezone.utc)


def iso(t):
    return t.isoformat(timespec="seconds")


def new_ledger(now):
    return {
        "version": 2, "unit": "API-equivalent USD",
        "cap_pct": CAP_PCT, "warn_pct": WARN_PCT,
        "calibration": {"pct_per_usd": PLACEHOLDER_PCT_PER_USD,
                        "calibrated": False,
                        "note": "placeholder, not measured"},
        "resets_at": iso(now + WEEK), "resets_at_source": "guess",
        "week_started": iso(now),
        "week": {r: {} for r in ROLES}, "free": {},
        "usage_readings": [], "past_weeks": [], "refusals": [],
        "pending": {}}


def tokens_of(usage):
    return sum(int(usage.get(k) or 0) for k in TOKEN_FIELDS)


def by_model(result, model):
    """{model: {the four token fields, cost_usd}} from a Claude Code JSON
    result: `modelUsage` when present, else `usage` and `total_cost_usd`
    under `model`."""
    out = {}
    for m, u in (result.get("modelUsage") or {}).items():
        out[m] = {v: int(u.get(k) or 0) for k, v in MODEL_FIELDS.items()}
        out[m]["cost_usd"] = float(u.get("costUSD") or 0)
    if not out and result.get("usage"):
        u = result["usage"]
        out[model] = {k: int(u.get(k) or 0) for k in TOKEN_FIELDS}
        out[model]["cost_usd"] = float(result.get("total_cost_usd") or 0)
    return out


class Ledger:
    """The ledger file, read and written under a lock for each
    operation.  `now` is a function (tests pass a fake clock)."""

    def __init__(self, path=PATH, now=now_utc):
        self.path = path
        self.now = now

    @contextlib.contextmanager
    def _open(self):
        os.makedirs(os.path.dirname(self.path), exist_ok=True)
        with open(self.path + ".lock", "w") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            if os.path.exists(self.path):
                d = json.load(open(self.path))
            else:
                d = new_ledger(self.now())
            self._roll(d)
            yield d
            tmp = self.path + ".tmp"
            with open(tmp, "w") as f:
                json.dump(d, f, indent=1)
            os.replace(tmp, self.path)

    def _roll(self, d):
        """Apply the weekly reset(s) that are due, and drop reservations
        older than PENDING_TTL (their run died before charging)."""
        t = self.now()
        d.setdefault("pending", {})
        for k, p in list(d["pending"].items()):
            if t - dt.datetime.fromisoformat(p["at"]) > PENDING_TTL:
                del d["pending"][k]
        while t >= dt.datetime.fromisoformat(d["resets_at"]):
            end = dt.datetime.fromisoformat(d["resets_at"])
            d["past_weeks"].append({
                "started": d["week_started"], "ended": iso(end),
                "usd": round(self._usd(d), 6),
                "pct": round(self._pct(d), 3),
                "week": d["week"], "free": d["free"]})
            d["week"] = {r: {} for r in ROLES}
            d["free"] = {}
            d["week_started"] = iso(end)
            d["resets_at"] = iso(end + WEEK)
            d["resets_at_source"] = "previous reset + 7 days"

    # ---- reading --------------------------------------------------------

    @staticmethod
    def _sum(d, key, role=None):
        return sum(m[key] for r, ms in d["week"].items()
                   if role in (None, r) for m in ms.values())

    @staticmethod
    def _usd(d, role=None):
        return Ledger._sum(d, "cost_usd", role)

    @staticmethod
    def _pending(d):
        return sum(p["est_usd"] for p in d.get("pending", {}).values())

    @staticmethod
    def _pct(d, usd=None):
        u = Ledger._usd(d) if usd is None else usd
        return u * d["calibration"]["pct_per_usd"]

    def snapshot(self):
        with self._open() as d:
            return copy.deepcopy(d)

    def summary(self):
        d = self.snapshot()
        return {"usd": round(self._usd(d), 4),
                "usd_by_role": {r: round(self._usd(d, r), 4)
                                for r in ROLES},
                "tokens": self._sum(d, "tokens"),
                "pending_usd": round(self._pending(d), 4),
                "pct": round(self._pct(d), 3),
                "cap_pct": d["cap_pct"], "warn_pct": d["warn_pct"],
                "resets_at": d["resets_at"],
                "calibrated": d["calibration"]["calibrated"],
                "pct_per_usd": d["calibration"]["pct_per_usd"]}

    # ---- the hard stop --------------------------------------------------

    def reserve(self, role, model, est_usd):
        """May a call whose cap is `est_usd` go ahead?  {ok, id, pct,
        projected_pct, cap_pct, warning, calibrated, ...}.  The projection
        counts the reservations of calls still in flight (other runs
        too), and an accepted call's `est_usd` stays reserved, under the
        same lock, until `charge(..., reservation=id)` or `release(id)`.
        A refusal is recorded in the ledger."""
        assert role in ROLES, role
        with self._open() as d:
            pct = self._pct(d)
            proj = self._pct(d, self._usd(d) + self._pending(d) + est_usd)
            r = {"ok": proj <= d["cap_pct"], "pct": round(pct, 3),
                 "projected_pct": round(proj, 3), "cap_pct": d["cap_pct"],
                 "warn_pct": d["warn_pct"], "role": role, "model": model,
                 "est_usd": est_usd,
                 "calibrated": d["calibration"]["calibrated"],
                 "warning": proj >= d["warn_pct"]}
            if r["ok"]:
                r["id"] = uuid.uuid4().hex
                d["pending"][r["id"]] = {"role": role, "model": model,
                                         "est_usd": est_usd,
                                         "at": iso(self.now())}
            else:
                d["refusals"].append({"at": iso(self.now()), **r})
        return r

    def release(self, reservation):
        """Drop a reservation whose call never ran."""
        with self._open() as d:
            d["pending"].pop(reservation, None)

    def charge(self, role, model_usage, est_usd=None, model=None,
               reservation=None):
        """Book a call's usage, {model: {token fields, cost_usd}}, and
        drop its reservation.  A call with no usage reported (killed, or
        no JSON) is charged its cap, `est_usd`, under `model`.  Returns
        {usd, tokens, pct, warning}."""
        assert role in ROLES, role
        if not model_usage:
            model_usage = {model or "(unknown)": {
                "cost_usd": est_usd or 0.0, "estimated": True}}
        with self._open() as d:
            d["pending"].pop(reservation, None)
            usd = tokens = 0
            for m, u in model_usage.items():
                e = d["week"][role].setdefault(m, {
                    "calls": 0, "tokens": 0, "cost_usd": 0.0,
                    **{k: 0 for k in TOKEN_FIELDS}})
                e["calls"] += 1
                n = tokens_of(u)
                e["tokens"] += n
                tokens += n
                for k in TOKEN_FIELDS:
                    e[k] += int(u.get(k) or 0)
                c = float(u.get("cost_usd") or 0)
                e["cost_usd"] = round(e["cost_usd"] + c, 6)
                usd += c
                if u.get("estimated"):
                    e["estimated_calls"] = e.get("estimated_calls", 0) + 1
            pct = self._pct(d)
            return {"usd": round(usd, 6), "tokens": tokens,
                    "pct": round(pct, 3), "warning": pct >= d["warn_pct"]}

    def log_free(self, model, usage):
        """Log a free model's tokens ({prompt_tokens, completion_tokens});
        nothing is charged."""
        with self._open() as d:
            e = d["free"].setdefault(model, {"calls": 0})
            e["calls"] += 1
            for k, v in (usage or {}).items():
                if isinstance(v, (int, float)):
                    e[k] = e.get(k, 0) + v

    # ---- /usage and calibration ----------------------------------------

    def record_reading(self, reading, label=""):
        """Store a /usage reading; its reset time becomes the ledger's."""
        if not reading:
            return
        with self._open() as d:
            d["usage_readings"].append({"label": label,
                                        "ledger_usd": round(self._usd(d), 6),
                                        **reading})
            d["usage_readings"] = d["usage_readings"][-200:]
            if reading.get("resets_at"):
                d["resets_at"] = reading["resets_at"]
                d["resets_at_source"] = "/usage"
                self._roll(d)

    def calibrate(self, percent, usd, since, source):
        """Record pct_per_usd = percent / usd, with its inputs."""
        if percent <= 0 or usd <= 0:
            raise ValueError("calibration needs a positive % and cost")
        with self._open() as d:
            d["calibration"] = {
                "pct_per_usd": percent / usd, "calibrated": True,
                "percent": percent, "usd": usd, "since": since,
                "source": source, "at": iso(self.now())}
            return d["calibration"]


class RunCap:
    """A ledger with a cap on one run's own spending (harness.py
    --max-usd): a call is refused when this run's charges, its
    reservations in flight and the call's cap together would pass
    `max_usd`.  Everything else goes to the ledger, which still applies
    the weekly cap."""

    def __init__(self, ledger, max_usd):
        self.ledger, self.max_usd = ledger, max_usd
        self.spent, self.held = 0.0, {}

    def __getattr__(self, name):
        return getattr(self.ledger, name)

    def reserve(self, role, model, est_usd):
        run = self.spent + sum(self.held.values()) + est_usd
        if run > self.max_usd + 1e-9:
            r = {"ok": False, "role": role, "model": model,
                 "est_usd": est_usd, "run_cap_usd": self.max_usd,
                 "run_spent_usd": round(self.spent, 4),
                 "run_projected_usd": round(run, 4),
                 "error": f"run cap: ${run:.2f} would pass this run's "
                          f"${self.max_usd:.2f} (--max-usd)"}
            return r
        r = self.ledger.reserve(role, model, est_usd)
        if r["ok"]:
            self.held[r["id"]] = est_usd
        return r

    def release(self, reservation):
        self.held.pop(reservation, None)
        self.ledger.release(reservation)

    def charge(self, role, model_usage, est_usd=None, model=None,
               reservation=None):
        self.held.pop(reservation, None)
        c = self.ledger.charge(role, model_usage, est_usd=est_usd,
                               model=model, reservation=reservation)
        self.spent += c["usd"]
        return c


USAGE_RX = re.compile(
    r"Current week \(all models\):\s*(\d+(?:\.\d+)?)% used"
    r"(?:\s*·\s*resets\s+([^(\n]+?)\s*\(([^)]+)\))?")


def parse_usage(text, now=None):
    """{pct, resets_at, at} from the text of Claude Code's /usage, or
    None.  The reset is given without a year ("Nov 6, 1:59am"): the next
    such time."""
    m = USAGE_RX.search(text or "")
    if not m:
        return None
    now = now or now_utc()
    out = {"pct": float(m.group(1)), "at": iso(now)}
    if m.group(2):
        try:
            from zoneinfo import ZoneInfo
            tz = ZoneInfo(m.group(3))
            local = now.astimezone(tz)
            s = m.group(2).strip()
            fmt = "%Y %b %d, %I:%M%p" if ":" in s else "%Y %b %d, %I%p"
            t = dt.datetime.strptime(f"{local.year} {s}", fmt) \
                .replace(tzinfo=tz)
            if t < local - dt.timedelta(days=1):
                t = t.replace(year=local.year + 1)
            out["resets_at"] = iso(t.astimezone(dt.timezone.utc))
        except Exception:  # an unknown format: keep the percentage
            pass
    return out


def weekly_usage(timeout=60):
    """The owner's weekly usage, read with `claude -p /usage` (a local
    command: no model call, no tokens).  {pct, resets_at, at} or None."""
    try:
        r = subprocess.run(["claude", "-p", "/usage", "--output-format",
                            "json", "--no-session-persistence"],
                           capture_output=True, text=True, timeout=timeout,
                           cwd=ARIADNE, stdin=subprocess.DEVNULL)
        res = json.loads(r.stdout)
    except Exception:
        return None
    if res.get("is_error") or res.get("num_turns"):
        return None
    return parse_usage(res.get("result", ""))


def ccusage_cost(report):
    """API-equivalent USD in a `ccusage claude daily --json` report: its
    `totals.totalCost`, else the sum of the days' `totalCost`."""
    t = (report.get("totals") or {}).get("totalCost")
    if t is not None:
        return float(t)
    days = report.get("daily")
    if days is None:
        raise ValueError("no totals.totalCost or daily[] in ccusage's "
                         f"output (keys: {sorted(report)})")
    return float(sum(x.get("totalCost") or 0 for x in days))


def run_ccusage(since):
    """ccusage's report for all Claude Code use on this machine since
    `since` (YYYY-MM-DD)."""
    r = subprocess.run(CCUSAGE + ["--since", since.replace("-", "")],
                       capture_output=True, text=True, timeout=600,
                       stdin=subprocess.DEVNULL)
    if r.returncode:
        raise RuntimeError("ccusage failed: " + r.stderr[-600:])
    return json.loads(r.stdout)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--ledger", default=PATH)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("show")
    sub.add_parser("usage")
    c = sub.add_parser("calibrate", help="pct_per_usd = the weekly % of "
                       "/usage over ccusage's cost since the reset")
    c.add_argument("--percent", type=float, required=True,
                   help="the weekly % (all models) /usage shows now")
    c.add_argument("--since", required=True,
                   help="the day of the last weekly reset, YYYY-MM-DD")
    c.add_argument("--usd", type=float,
                   help="the cost, instead of running ccusage")
    a = ap.parse_args()
    L = Ledger(a.ledger)
    if a.cmd == "show":
        print(json.dumps(L.summary(), indent=1))
    elif a.cmd == "usage":
        u = weekly_usage()
        print(json.dumps(u))
        L.record_reading(u, "budget.py usage")
    else:
        if a.usd is None:
            usd, src = ccusage_cost(run_ccusage(a.since)), " ".join(CCUSAGE)
        else:
            usd, src = a.usd, "--usd"
        print(json.dumps(L.calibrate(a.percent, usd, a.since, src),
                         indent=1))


if __name__ == "__main__":
    main()
