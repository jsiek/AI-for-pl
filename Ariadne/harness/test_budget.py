"""Offline tests of the budget ledger (budget.py): refusal at the 20%
cap, the warning at 15%, the weekly reset, free models not charged, a
killed call charged its cap, calibration, and the parsers of /usage,
Claude Code's JSON result and ccusage's report.  No model calls.

    python3 test_budget.py
"""
import datetime as dt
import os
import shutil
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import budget  # noqa: E402

fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800].replace("\n", "\n    "))


class Clock:
    def __init__(self, t):
        self.t = t

    def __call__(self):
        return self.t


T0 = dt.datetime(2026, 11, 2, 12, 0, tzinfo=dt.timezone.utc)
USE = {"claude-sonnet-5-5": {"input_tokens": 10, "output_tokens": 1000,
                             "cache_creation_input_tokens": 5000,
                             "cache_read_input_tokens": 30000,
                             "cost_usd": 1.0}}
tmp = tempfile.mkdtemp()
try:
    clock = Clock(T0)
    L = budget.Ledger(os.path.join(tmp, "budget.json"), now=clock)
    s = L.summary()
    expect("new ledger: empty, uncalibrated placeholder, caps 20/15",
           s["usd"] == 0 and not s["calibrated"]
           and s["pct_per_usd"] == budget.PLACEHOLDER_PCT_PER_USD
           and (s["cap_pct"], s["warn_pct"]) == (20.0, 15.0), s)
    # Placeholder 2% per USD: the cap is $10, the warning $7.50.
    r = L.reserve("prover", "claude-sonnet-5-5", 1.0)
    expect("reserve under the cap", r["ok"] and not r["warning"], r)
    for _ in range(7):
        c = L.charge("prover", USE)
    expect("charge books USD and all four token kinds",
           L.summary()["usd"] == 7.0 and c["tokens"] == 36010
           and L.summary()["tokens"] == 7 * 36010, L.summary())
    expect("no warning at 14%", not c["warning"] and c["pct"] == 14.0, c)
    r = L.reserve("prover", "claude-sonnet-5-5", 1.0)
    expect("warning when the call may reach 15%",
           r["ok"] and r["warning"] and r["projected_pct"] == 16.0, r)
    c = L.charge("prover", USE)
    expect("warning at 16% after the charge", c["warning"], c)
    L.charge("annotator", USE)
    r = L.reserve("prover", "claude-sonnet-5-5", 1.0)
    expect("reserve up to exactly the cap (18% + 2%)", r["ok"], r)
    r = L.reserve("prover", "claude-sonnet-5-5", 1.5)
    expect("refused past the cap (18% + 3%)",
           not r["ok"] and r["projected_pct"] == 21.0, r)
    snap = L.snapshot()
    expect("the refusal is recorded", len(snap["refusals"]) == 1,
           snap["refusals"])
    expect("roles kept apart",
           L.summary()["usd_by_role"] == {"prover": 8.0, "annotator": 1.0},
           L.summary())
    L.log_free("glm-5.3-flash", {"prompt_tokens": 60000,
                                 "completion_tokens": 3000})
    expect("free model logged, not charged",
           L.summary()["usd"] == 9.0
           and L.snapshot()["free"]["glm-5.3-flash"]["prompt_tokens"]
           == 60000, L.snapshot()["free"])
    c = L.charge("prover", {}, est_usd=1.0, model="claude-sonnet-5-5")
    e = L.snapshot()["week"]["prover"]["claude-sonnet-5-5"]
    expect("a call with no usage is charged its cap",
           c["usd"] == 1.0 and e.get("estimated_calls") == 1, e)
    # The weekly reset.
    clock.t = T0 + dt.timedelta(days=7, seconds=1)
    s = L.summary()
    snap = L.snapshot()
    expect("weekly reset: totals cleared, week archived",
           s["usd"] == 0 and len(snap["past_weeks"]) == 1
           and snap["past_weeks"][0]["usd"] == 10.0
           and snap["free"] == {}, snap["past_weeks"])
    r = L.reserve("prover", "claude-sonnet-5-5", 1.0)
    expect("after the reset calls are allowed again", r["ok"], r)
    clock.t = T0 + dt.timedelta(days=22)
    s = L.summary()
    expect("two missed resets roll twice",
           len(L.snapshot()["past_weeks"]) == 3
           and dt.datetime.fromisoformat(s["resets_at"]) > clock.t, s)
    # A /usage reading sets the reset time.
    L.record_reading({"pct": 30.0, "resets_at": budget.iso(
        clock.t + dt.timedelta(days=2))}, "test")
    expect("a /usage reading sets resets_at",
           L.snapshot()["resets_at_source"] == "/usage", L.snapshot())
    cal = L.calibrate(22.0, 110.0, "2026-11-01", "test")
    s = L.summary()
    expect("calibration: 22% over $110 = 0.2% per USD, stored with inputs",
           s["calibrated"] and abs(s["pct_per_usd"] - 0.2) < 1e-9
           and cal["since"] == "2026-11-01" and cal["usd"] == 110.0, cal)
finally:
    shutil.rmtree(tmp)

# Parsers.
text = ("Current session: 9% used · resets Nov 4, 11:09pm (America/"
        "Indiana/Indianapolis)\nCurrent week (all models): 22% used · "
        "resets Nov 6, 1:59am (America/Indiana/Indianapolis)\n")
u = budget.parse_usage(text, now=dt.datetime(2026, 11, 5, 3, 0,
                                             tzinfo=dt.timezone.utc))
expect("parse /usage: weekly % and reset (EST, UTC-5)",
       u["pct"] == 22.0 and u["resets_at"] == "2026-11-06T06:59:00+00:00", u)
u = budget.parse_usage(
    "Current week (all models): 3% used · resets Jan 2, 2am (UTC)",
    now=dt.datetime(2026, 12, 30, tzinfo=dt.timezone.utc))
expect("parse /usage: reset across the new year",
       u["resets_at"] == "2027-01-02T02:00:00+00:00", u)
expect("parse /usage: no weekly line gives None",
       budget.parse_usage("Current session: 9% used") is None)
res = {"total_cost_usd": 0.0247, "usage": {"input_tokens": 2},
       "modelUsage": {"claude-sonnet-5-5": {
           "inputTokens": 2, "outputTokens": 4,
           "cacheReadInputTokens": 3396, "cacheCreationInputTokens": 6068,
           "costUSD": 0.0247}}}
m = budget.by_model(res, "x")
expect("by_model reads modelUsage",
       m == {"claude-sonnet-5-5": {
           "input_tokens": 2, "output_tokens": 4,
           "cache_read_input_tokens": 3396,
           "cache_creation_input_tokens": 6068, "cost_usd": 0.0247}}, m)
m = budget.by_model({"total_cost_usd": 0.5, "usage": {
    "input_tokens": 1, "output_tokens": 2}}, "claude-sonnet-5-5")
expect("by_model falls back to usage and total_cost_usd",
       m["claude-sonnet-5-5"]["cost_usd"] == 0.5, m)
expect("ccusage: totals.totalCost",
       budget.ccusage_cost({"daily": [], "totals": {"totalCost": 12.5}})
       == 12.5)
expect("ccusage: sum of daily totalCost",
       budget.ccusage_cost({"daily": [{"totalCost": 1.5},
                                      {"totalCost": 2.0}]}) == 3.5)
print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
