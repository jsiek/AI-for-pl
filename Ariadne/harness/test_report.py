"""Offline test of the run report (harness.py write / markdown): a run
that stops at its --max-usd cap must still end with report.json, a
complete report.md and the `verdict:` line; step 0's appended log is
judged per run.  No model calls, no image.

wp-run2 (plan Q10) crashed here: markdown() read `projected_pct` from
every budget refusal, but a run-cap refusal (budget.RunCap) has
`error` instead, so report.md was cut short and no verdict was logged.

    python3 test_report.py
"""
import contextlib
import io
import json
import os
import shutil
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import budget  # noqa: E402
import harness  # noqa: E402

fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800].replace("\n", "\n    "))


tmp = tempfile.mkdtemp(prefix="test_report_")
try:
    # Refusals as the two gates write them: the run cap and the weekly cap.
    rc = budget.RunCap(budget.Ledger(os.path.join(tmp, "l.json")), 1.0)
    rc.spent = 0.99
    run_cap = rc.reserve("annotator", "claude-opus-5-5", 3.0)
    weekly = budget.Ledger(os.path.join(tmp, "w.json")).reserve(
        "prover", "claude-opus-5-5", 1e6)
    expect("both gates refuse", not run_cap["ok"] and not weekly["ok"],
           (run_cap, weekly))
    census = {"goals": 2, "proved": 1, "qed": 1, "smt": 0, "coq": 0,
              "open": 1, "smt_by_prover": {}}
    report = {
        "benchmark": "/x/bench/b1a", "blank_coq": False, "llm_calls": 1,
        "verdict": "failed", "seconds": 1.0, "census": census,
        "census_after_wp": census, "steps": {"3_wp": {"ok": True}},
        "guardrails": {"goal_accounting": {"ok": False}},
        "goals": [{"goal": "typed_b1_assert", "line": 3,
                   "discharger": "open"}],
        "budget": {"usd_charged": 0.99, "tokens_charged": 10,
                   "warnings": [], "end": {},
                   "refused": [{"goal": "(annotator)", **run_cap},
                               {"goal": "typed_lemma_x", **weekly}]},
        "failure": {"guardrails_failed": ["goal_accounting"],
                    "steps_failed": [], "open_goals": ["typed_b1_assert"]}}

    class Stub:  # what Run.write uses
        dir = tmp

        def __init__(self):
            self.report = report

        def log(self, msg):
            print(msg)

    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        harness.Run.write(Stub())
    md = open(os.path.join(tmp, "report.md")).read()
    expect("report.md is complete with a run-cap refusal",
           "run cap: $0.01 left" in md and "% would pass the" in md
           and md.rstrip().endswith("No certificate was produced."), md)
    expect("report.json is written",
           json.load(open(os.path.join(tmp, "report.json")))["verdict"]
           == "failed")
    expect("the verdict line is logged",
           "verdict: failed;" in out.getvalue(), out.getvalue())
    # Step 0's log holds one run per patch; only the last one counts.
    log = ("$ sh ./check.sh\nFAIL: E-ACSL run of the source:\n"
           "FAIL: runtime checking of B1c\n"
           "$ sh ./check.sh\nPASS: ASan+UBSan build\n"
           "FAIL: E-ACSL build of the source:\n")
    last = harness.last_run(log)
    fl = [x for x in last.splitlines() if x.startswith("FAIL")]
    expect("step 0: a patch is judged by its own run (inconclusive)",
           harness.rac_outcome({"ok": False, "fail_lines": fl})
           == "inconclusive", fl)
finally:
    shutil.rmtree(tmp)
print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
