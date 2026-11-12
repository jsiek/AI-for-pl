"""Offline tests of run_vst.py's budget gate, with a fake `claude`: the
call's cap is reserved in the ledger before the call, a ledger that
cannot take it refuses the run before any model call, and an accepted
call is charged against its reservation.  No model calls, no image.

    python3 test_run_vst.py
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "harness"))
import budget  # noqa: E402

fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800].replace("\n", "\n    "))


tmp = tempfile.mkdtemp(prefix="test_run_vst_")
try:
    bindir = os.path.join(tmp, "bin")
    os.makedirs(bindir)
    marker = os.path.join(tmp, "claude_ran")
    with open(os.path.join(bindir, "claude"), "w") as f:
        f.write(f"""#!{sys.executable}
import json
open({marker!r}, "a").write("ran\\n")
print(json.dumps({{"subtype": "success", "num_turns": 2,
  "total_cost_usd": 1.25, "result": "done", "permission_denials": [],
  "modelUsage": {{"claude-opus-5-5": {{"inputTokens": 1,
    "outputTokens": 2, "cacheCreationInputTokens": 3,
    "cacheReadInputTokens": 4, "costUSD": 1.25}}}}}}))
""")
    os.chmod(os.path.join(bindir, "claude"), 0o755)
    env = dict(os.environ, PATH=bindir + os.pathsep + os.environ["PATH"])

    def run(name, ledger):
        return subprocess.run(
            [sys.executable, os.path.join(HERE, "run_vst.py"),
             "--run-dir", os.path.join(tmp, name), "--ledger", ledger,
             "--usd", "15"], env=env, capture_output=True, text=True)

    # Placeholder 2%/USD and a 20% cap: a $15 call (30%) is refused.
    low = os.path.join(tmp, "low.json")
    budget.Ledger(low).summary()
    p = run("refused", low)
    expect("ledger refuses a $15 call: exit non-zero, claude never runs",
           p.returncode != 0 and not os.path.exists(marker)
           and "refused" in p.stderr, (p.returncode, p.stderr[-300:]))
    gate = json.load(open(os.path.join(tmp, "refused", "budget_gate.json")))
    s = budget.Ledger(low).summary()
    expect("the refusal is recorded; nothing charged or held",
           not gate["ok"] and s["usd"] == 0 and s["pending_usd"] == 0,
           (gate, s))
    # Calibrated at 0.089% per USD: $15 is 1.3%, accepted.
    ok = os.path.join(tmp, "ok.json")
    budget.Ledger(ok).calibrate(23.0, 258.54, "2026-11-01", "test")
    p = run("accepted", ok)
    s = budget.Ledger(ok).summary()
    expect("calibrated ledger: claude runs once, its cost is charged and "
           "the reservation dropped",
           p.returncode == 0 and open(marker).read() == "ran\n"
           and s["usd"] == 1.25 and s["pending_usd"] == 0, (p.stderr, s))
finally:
    shutil.rmtree(tmp)
print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
