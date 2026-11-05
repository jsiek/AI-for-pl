#!/usr/bin/env python3
"""The Anthropic budget ledger (plan section 11, item 3).

`Ariadne/runs/budget.json` (git-ignored) holds the Anthropic tokens the
pipeline used since the last weekly reset, by role (prover, annotator)
and by model.  Before each Claude call the caller asks `reserve` with an
estimate of the call's cost (its per-goal cap); the call is refused if
the week's total would pass the cap.  After the call, `charge` books the
tokens it used.  Free models (GLM on REALLMS) are logged with
`log_free` and never charged.

Percentages are of the owner's weekly usage limit.  Tokens are turned
into percent through a calibration factor, `pct_per_mtok` (% of the
weekly limit per million tokens), stored in the ledger.  Until it is
calibrated, a conservative placeholder is used (PLACEHOLDER_PCT_PER_MTOK)
and every report says so.  The cap is 20% and the warning 15%.

A token, for the ledger, is any of input, output, cache-creation and
cache-read tokens, as Claude Code's JSON result reports them (`usage` /
`modelUsage`); the components and the list-price `costUSD` are kept too,
so the measure can be changed later.

The week resets at `resets_at`: totals move to `past_weeks` and the next
reset is a week later.  `resets_at` comes from Claude Code's `/usage`
(`weekly_usage()`) when it can be read, else a week after the ledger was
created.

    python3 ledger.py show
    python3 ledger.py usage                  # read /usage (no model call)
    python3 ledger.py calibrate REPORT.json  # factor from a run's readings
    python3 ledger.py calibrate --pct D --tokens N
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
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ARIADNE = os.path.dirname(HERE)
PATH = os.path.join(ARIADNE, "runs", "budget.json")

CAP_PCT = 20.0
WARN_PCT = 15.0
# Not measured: 10% per million tokens puts the cap at 2M tokens, about
# 40 Sonnet goals at B1's 40-50k tokens each.  Deliberately high, so an
# uncalibrated ledger refuses early rather than late.
PLACEHOLDER_PCT_PER_MTOK = 10.0
WEEK = dt.timedelta(days=7)
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


def new_ledger(now, resets_at=None):
    return {
        "version": 1, "cap_pct": CAP_PCT, "warn_pct": WARN_PCT,
        "calibration": {"pct_per_mtok": PLACEHOLDER_PCT_PER_MTOK,
                        "calibrated": False,
                        "note": "placeholder, not measured"},
        "resets_at": iso(resets_at or now + WEEK),
        "resets_at_source": "/usage" if resets_at else "guess",
        "week_started": iso(now),
        "week": {r: {} for r in ROLES}, "free": {},
        "usage_readings": [], "past_weeks": [], "refusals": []}


def tokens_of(usage):
    """Total tokens of a {field: n} dict (snake_case fields)."""
    return sum(int(usage.get(k) or 0) for k in TOKEN_FIELDS)


def by_model(result, model):
    """{model: {the four token fields, cost_usd}} from a Claude Code JSON
    result: `modelUsage` when present, else `usage` under `model`."""
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
        """Apply the weekly reset(s) that are due."""
        t = self.now()
        while t >= dt.datetime.fromisoformat(d["resets_at"]):
            end = dt.datetime.fromisoformat(d["resets_at"])
            d["past_weeks"].append({
                "started": d["week_started"], "ended": iso(end),
                "pct": round(self._pct(d), 3),
                "week": d["week"], "free": d["free"]})
            d["week"] = {r: {} for r in ROLES}
            d["free"] = {}
            d["week_started"] = iso(end)
            d["resets_at"] = iso(end + WEEK)
            d["resets_at_source"] = "previous reset + 7 days"

    # ---- reading --------------------------------------------------------

    @staticmethod
    def _tokens(d, role=None):
        return sum(m["tokens"] for r, ms in d["week"].items()
                   if role in (None, r) for m in ms.values())

    @staticmethod
    def _pct(d, tokens=None):
        t = Ledger._tokens(d) if tokens is None else tokens
        return t / 1e6 * d["calibration"]["pct_per_mtok"]

    def snapshot(self):
        """The ledger, with the week's totals in tokens and percent."""
        with self._open() as d:
            s = copy.deepcopy(d)
        s["tokens"] = self._tokens(s)
        s["tokens_by_role"] = {r: self._tokens(s, r) for r in ROLES}
        s["pct"] = round(self._pct(s), 3)
        return s

    def summary(self):
        s = self.snapshot()
        return {k: s[k] for k in ("tokens", "tokens_by_role", "pct",
                                  "cap_pct", "warn_pct", "resets_at")} | {
            "calibrated": s["calibration"]["calibrated"],
            "pct_per_mtok": s["calibration"]["pct_per_mtok"]}

    # ---- the hard stop --------------------------------------------------

    def reserve(self, role, model, est_tokens):
        """May a call estimated at `est_tokens` go ahead?  {ok, pct,
        projected_pct, cap_pct, warning, calibrated}.  A refusal is
        recorded in the ledger."""
        assert role in ROLES, role
        with self._open() as d:
            pct = self._pct(d)
            proj = self._pct(d, self._tokens(d) + est_tokens)
            r = {"ok": proj <= d["cap_pct"], "pct": round(pct, 3),
                 "projected_pct": round(proj, 3), "cap_pct": d["cap_pct"],
                 "warn_pct": d["warn_pct"], "role": role, "model": model,
                 "est_tokens": est_tokens,
                 "calibrated": d["calibration"]["calibrated"]}
            r["warning"] = proj >= d["warn_pct"]
            if not r["ok"]:
                d["refusals"].append({"at": iso(self.now()), **r})
        return r

    def charge(self, role, model_usage, est_tokens=None, note=None):
        """Book a call's usage, {model: {token fields, cost_usd}}; with no
        usage (a killed call), `est_tokens` under the key "(estimate)" of
        the model given as `note`.  Returns {tokens, pct, warning}."""
        assert role in ROLES, role
        if not model_usage and est_tokens:
            model_usage = {note or "(unknown)": {
                "input_tokens": est_tokens, "estimated": True}}
        with self._open() as d:
            spent = 0
            for m, u in model_usage.items():
                e = d["week"][role].setdefault(m, {
                    "calls": 0, "tokens": 0, "cost_usd": 0.0,
                    **{k: 0 for k in TOKEN_FIELDS}})
                e["calls"] += 1
                n = tokens_of(u)
                e["tokens"] += n
                spent += n
                for k in TOKEN_FIELDS:
                    e[k] += int(u.get(k) or 0)
                e["cost_usd"] = round(e["cost_usd"]
                                      + float(u.get("cost_usd") or 0), 6)
                if u.get("estimated"):
                    e["estimated_calls"] = e.get("estimated_calls", 0) + 1
            pct = self._pct(d)
            return {"tokens": spent, "pct": round(pct, 3),
                    "warning": pct >= d["warn_pct"]}

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
                                        "tokens": self._tokens(d),
                                        **reading})
            d["usage_readings"] = d["usage_readings"][-200:]
            if reading.get("resets_at"):
                d["resets_at"] = reading["resets_at"]
                d["resets_at_source"] = "/usage"

    def calibrate(self, pct_delta, tokens, source):
        if tokens <= 0 or pct_delta <= 0:
            raise ValueError("calibration needs a positive % and tokens")
        with self._open() as d:
            d["calibration"] = {"pct_per_mtok": pct_delta / (tokens / 1e6),
                                "calibrated": True, "pct_delta": pct_delta,
                                "tokens": tokens, "source": source,
                                "at": iso(self.now())}
            return d["calibration"]


USAGE_RX = re.compile(
    r"Current week \(all models\):\s*(\d+(?:\.\d+)?)% used"
    r"(?:\s*·\s*resets\s+([^(\n]+?)\s*\(([^)]+)\))?")


def parse_usage(text, now=None):
    """{pct, resets_at} from the text of Claude Code's /usage, or None.
    The reset is given without a year ("Nov 6, 1:59am"): the next such
    time after `now`."""
    m = USAGE_RX.search(text or "")
    if not m:
        return None
    out = {"pct": float(m.group(1)), "at": iso(now or now_utc())}
    if m.group(2):
        try:
            from zoneinfo import ZoneInfo
            tz = ZoneInfo(m.group(3))
            now = (now or now_utc()).astimezone(tz)
            s = m.group(2).strip()
            fmt = "%Y %b %d, %I:%M%p" if ":" in s else "%Y %b %d, %I%p"
            t = dt.datetime.strptime(f"{now.year} {s}", fmt) \
                .replace(tzinfo=tz)
            if t < now - dt.timedelta(days=1):
                t = t.replace(year=now.year + 1)
            out["resets_at"] = iso(t.astimezone(dt.timezone.utc))
        except Exception:  # an unknown format: keep the percentage
            pass
    return out


def weekly_usage(cwd=None, timeout=60):
    """The owner's weekly usage, read with `claude -p /usage` (a local
    command: no model call, no tokens).  {pct, resets_at, at} or None."""
    try:
        r = subprocess.run(["claude", "-p", "/usage", "--output-format",
                            "json", "--no-session-persistence"],
                           capture_output=True, text=True, timeout=timeout,
                           cwd=cwd or ARIADNE)
        res = json.loads(r.stdout)
    except Exception:
        return None
    if res.get("is_error") or res.get("num_turns"):
        return None
    return parse_usage(res.get("result", ""))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--ledger", default=PATH)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("show")
    sub.add_parser("usage")
    c = sub.add_parser("calibrate")
    c.add_argument("report", nargs="?",
                   help="a run's report.json with /usage readings before "
                   "and after")
    c.add_argument("--pct", type=float)
    c.add_argument("--tokens", type=int)
    a = ap.parse_args()
    L = Ledger(a.ledger)
    if a.cmd == "show":
        print(json.dumps(L.summary(), indent=1))
    elif a.cmd == "usage":
        u = weekly_usage()
        print(json.dumps(u))
        L.record_reading(u, "ledger.py usage")
    else:
        if a.report:
            b = json.load(open(a.report))["budget"]
            pct = b["weekly_usage_after"]["pct"] - \
                b["weekly_usage_before"]["pct"]
            tokens, src = b["tokens_charged"], a.report
        else:
            pct, tokens, src = a.pct, a.tokens, "command line"
        print(json.dumps(L.calibrate(pct, tokens, src), indent=1))


if __name__ == "__main__":
    main()
