#!/usr/bin/env python3
"""Command-line version of reallms_coq.py's tools, for provers that run as
Claude Code subagents (tiers 2 and 3) instead of through REALLMS.  The
same checks and the same verdict as the REALLMS worker:

  prover_cli.py statement GOAL.v              the goal (proof hidden)
  prover_cli.py query GOAL.v 'Check nth_cons.'  one Search/Check/Print/...
  prover_cli.py goals GOAL.v SCRIPT.v         goals after a partial script
  prover_cli.py check GOAL.v SCRIPT.v         full proof: ok + coqc errors

SCRIPT.v holds only the text between Proof. and Qed.  Each call appends
one line to $PROVER_CLI_LOG (if set): the command and whether it passed,
so a run can be counted and audited.  `check` prints "OK: proof accepted
by coqc" on success.  With $PROVER_CLI_MAX_CALLS set (it needs the log),
a `goals` or `check` call past that many in the log is refused (exit 2)
without running.
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from reallms_coq import Worker  # noqa: E402


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    cmd, goal = sys.argv[1], sys.argv[2]
    log = os.environ.get("PROVER_CLI_LOG")
    cap = os.environ.get("PROVER_CLI_MAX_CALLS")
    if cap and log and cmd in ("goals", "check"):
        used = 0
        if os.path.exists(log):
            used = sum(json.loads(x)["cmd"] in ("goals", "check")
                       for x in open(log) if x.strip())
        if used >= int(cap):
            print(f"Budget used up: {cap} goals/check calls.  Stop now.")
            sys.exit(2)
    w = Worker(goal, timeout=120, fh=None, blank=True)
    t = time.time()
    if cmd == "statement":
        out, ok = w.statement(), True
    elif cmd == "query":
        out = w.coq_query(sys.argv[3])
        ok = not out.startswith("(")
    elif cmd in ("goals", "check"):
        script = open(sys.argv[3]).read()
        if cmd == "goals":
            out = w.show_goals(script)
            ok = w.goals_ok
        else:
            r = w.check_proof(script)
            ok = r["ok"]
            out = "OK: proof accepted by coqc" if ok else (
                r["errors"] + "\n\nGoal state just before the failing "
                "step:\n" + r.get("goal_state_before_failing_step", ""))
    else:
        sys.exit(__doc__)
    print(out)
    if log:
        with open(log, "a") as f:
            f.write(json.dumps({"cmd": cmd, "ok": ok,
                                "seconds": round(time.time() - t, 1)})
                    + "\n")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
