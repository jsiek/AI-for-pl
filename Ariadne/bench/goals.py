"""Print WP JSON reports' census and the goals that are not proved.

    python3 goals.py report.json [report2.json ...]

Census: goals proved by Qed (WP's simplifier), by each SMT prover, by Coq,
and not proved, as plan milestone M1 asks.  Exits 1 if any goal is open.
"""

import collections
import json
import sys


def main():
    goals = [g for path in sys.argv[1:] for g in json.load(open(path))]
    census = collections.Counter()
    open_goals = []
    for g in goals:
        if g["verdict"] == "valid":
            winners = [p["prover"] for p in g.get("provers", [])
                       if p.get("success")]
            census[winners[0] if winners else "valid"] += 1
        else:
            census["open"] += 1
            open_goals.append(g)
    proved = len(goals) - len(open_goals)
    print(f"{proved} / {len(goals)} goals proved; "
          + ", ".join(f"{k}: {v}" for k, v in sorted(census.items())))
    for g in open_goals:
        print(f"  {g.get('function', '(lemma)'):30s} {g['goal']} "
              f"(line {g['line']}, {g['verdict']})")
    return 1 if open_goals else 0


if __name__ == "__main__":
    sys.exit(main())
