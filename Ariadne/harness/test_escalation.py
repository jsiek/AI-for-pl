"""Offline test of the comparison budget in escalation.py: parallel paid
attempts hold their caps, so together they cannot pass --usd.  No model
calls.

    python3 test_escalation.py
"""
import os
import sys
import threading
import time
import types

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import escalation  # noqa: E402

fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800].replace("\n", "\n    "))


r = object.__new__(escalation.Runner)
r.rows, r.held = [], 0.0
r.a = types.SimpleNamespace(usd=escalation.CAPS[escalation.OPUS])


def fake(phase, model, goal, k, handoff):
    time.sleep(0.5)  # all three workers check the budget meanwhile
    row = {"phase": phase, "model": model, "goal": goal, "k": k,
           "usd": 0.4, "status": "proved"}
    with escalation.LOCK:
        r.rows.append(row)
    return row


r._attempt = fake
out = []
ts = [threading.Thread(target=lambda g=g: out.append(
    r.attempt("s1", escalation.OPUS, g))) for g in "abc"]
for t in ts:
    t.start()
for t in ts:
    t.join()
expect("three parallel Opus attempts under one cap: one runs",
       sorted(x["status"] for x in out)
       == ["proved"] + ["skipped: comparison budget"] * 2, out)
expect("the held caps are released", r.held == 0.0, r.held)
print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
