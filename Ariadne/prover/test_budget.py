"""Offline test of tool_loop's working-time budget (no model calls): a
fake model that never solves stops on time, not turns, and rate-limit
backoffs do not count against the budget.  Usage: python3 test_budget.py"""
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "scripts"))
import reallms_client  # noqa: E402

fails = []


def expect(name, cond, detail):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + detail)


def fake_chat(waited):
    """Each reply takes 0.2 s of work plus `waited` s of backoff."""
    def chat(*args, **kw):
        time.sleep(0.2 + waited)
        return {"content": "", "reasoning": "", "finish": "tool_calls",
                "usage": {}, "waited": waited,
                "tool_calls": [{"id": "c", "name": "check_proof",
                                "args": "{}"}]}
    return chat


def run(waited, max_seconds, max_steps=100):
    reallms_client.chat = fake_chat(waited)
    return reallms_client.tool_loop(
        "m", "k", "sys", "user", [], lambda n, a: "failed",
        solved=lambda: False, check_tool="check_proof", nudge="go",
        max_steps=max_steps, max_seconds=max_seconds)


r = run(0.0, 1)
expect("stops on time", r["status"] == "time_up" and 4 <= r["steps"] <= 6,
       str(r))
r = run(0.0, None, max_steps=10)
expect("no budget: stops on turns",
       r["status"] == "incomplete" and r["steps"] == 10, str(r))
# 0.4 s of wall clock per reply, half of it backoff: the budget charges
# only the 0.2 s of work, so the run gets as many turns as without waits.
r = run(0.2, 1)
expect("backoffs not charged", r["status"] == "time_up"
       and 4 <= r["steps"] <= 6 and r["waited"] >= 0.8, str(r))
sys.exit(1 if fails else 0)
