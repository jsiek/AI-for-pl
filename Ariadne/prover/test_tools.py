"""Offline test of reallms_coq.py's tools (no model calls) on a WP goal
file whose proof is known.  Usage: python3 test_tools.py <goal.v>"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from reallms_coq import Worker  # noqa: E402

w = Worker(sys.argv[1], timeout=120, fh=None)
fails = []


def expect(name, cond, detail):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + detail[:800].replace("\n", "\n    "))


r = w.check_proof(w.script)
expect("known proof accepted", r["ok"], r["errors"])
r = w.check_proof("intros. admit.")
expect("admit refused", not r["ok"] and "forbidden" in r["errors"], str(r))
r = w.check_proof("Qed. Theorem x : True. trivial.")
expect("early Qed refused", not r["ok"] and "forbidden" in r["errors"], str(r))
r = w.check_proof("intros.")
expect("incomplete proof refused", not r["ok"] and r["errors"], str(r))
out = w.show_goals("intros a l a1.")
expect("show_goals shows the goal", "P_mem" in out and "a1" in out, out)
# GLM's failing script from the first trial: the error is on line 4,
# and the state before it (after the bullet) must be shown.
bad = ("intros a l a1. split.\n- intros [Heq | Hmem].\n"
       "  + subst a1. exists 0%Z. rewrite length_cons. split.\n"
       "    * rewrite nth_cons.")
out = w.show_goals(bad)
expect("error line is script-relative", "script line 4," in out, out)
expect("state before failing step shown",
       "Goal state just before the failing step" in out
       and "nth (a :: l) 0" in out.replace("%Z", ""), out)
r = w.check_proof(bad)
expect("check_proof gives the state too",
       "nth (a :: l) 0" in r.get("goal_state_before_failing_step",
                                 "").replace("%Z", ""), str(r))
w.dispatch("coq_query", {"command": "Check nth_cons."})
out = w.dispatch("coq_query", {"command": "Check nth_cons."})
expect("repeated call flagged", out.startswith("(this is the same"), out)
out = w.coq_query("Print P_mem")
expect("coq_query Print", "P_mem" in out and "Error" not in out, out)
out = w.coq_query("Check length_cons. Admitted")
expect("coq_query one command only", out.startswith("(only one"), out)
out = w.read_file("bench/b1/b1.c", 1, 3)
expect("read_file", out.startswith("1: "), out)
try:
    w._safe("../../etc/passwd")
    expect("read_file confined", False, "escaped Ariadne/")
except ValueError:
    expect("read_file confined", True, "")
# --blank: the target's proof and its siblings' proofs are hidden from
# read_file and grep (a sibling's first proof line must not show).
b = Worker(sys.argv[1], timeout=120, fh=None, blank=True)
rel = os.path.relpath(b.path, os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))))
first = next(l for l in w.script.split("\n") if l.strip())
seen = b.read_file(rel, 1, 100000)
expect("blank: target proof hidden by read_file",
       "(* proof hidden *)" in seen and first not in seen, seen[-400:])
d = os.path.dirname(b.path)
sibs = [n for n in os.listdir(d) if n.endswith(".v")
        and os.path.join(d, n) != b.path]
leaks = []
for n in sibs:
    sib = Worker(os.path.join(d, n), timeout=120, fh=None)
    line = next(l for l in sib.script.split("\n") if len(l.strip()) > 8)
    if line in b.read_file(os.path.join(os.path.dirname(rel), n), 1, 100000):
        leaks.append(n)
expect(f"blank: {len(sibs)} sibling proofs hidden by read_file", not leaks,
       str(leaks))
out = b.grep(r"^\s*(intros|unfold|induction)\b", os.path.dirname(rel))
expect("blank: no proof lines from grep", out == "(no matches)", out)
print(f"{w.coqc_runs} coqc runs")
sys.exit(1 if fails else 0)
