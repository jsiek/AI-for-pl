"""Print WP JSON reports' census and the goals that are not proved.

    python3 goals.py report.json[:N] [report2.json[:N] ...]
    python3 goals.py --expect-open LINE[-LAST] REGEX report.json

Census: goals proved by Qed (WP's simplifier), by each SMT prover, by Coq,
and not proved, as plan milestone M1 asks.

Default mode exits 0 only if every goal is proved.  A report with no goals
is a failure (a filter that stops matching must not pass as "all
proved"), and `report.json:N` also requires exactly N goals in it.

--expect-open (for mutants) exits 0 only if at least one goal is open,
every open goal is on source line LINE (or LINE..LAST) and has a name
matching REGEX, and every other goal is proved: the mutant fails for the
intended reason and no other.
"""

import collections
import json
import re
import sys


def load(spec):
    """Goals of `path` or `path:N`; None (after a message) if wrong."""
    path, _, count = spec.partition(":")
    goals = json.load(open(path))
    if not goals:
        print(f"{path}: no goals (a filter matched nothing?)")
        return None
    if count and len(goals) != int(count):
        print(f"{path}: {len(goals)} goals, expected {count}")
        return None
    return goals


def census(goals):
    counts = collections.Counter()
    open_goals = []
    for g in goals:
        if g["verdict"] == "valid":
            winners = [p["prover"] for p in g.get("provers", [])
                       if p.get("success")]
            counts[winners[0] if winners else "valid"] += 1
        else:
            counts["open"] += 1
            open_goals.append(g)
    proved = len(goals) - len(open_goals)
    print(f"{proved} / {len(goals)} goals proved; "
          + ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())))
    for g in open_goals:
        print(f"  {g.get('function', '(lemma)'):30s} {g['goal']} "
              f"(line {g['line']}, {g['verdict']})")
    return open_goals


def main():
    args = sys.argv[1:]
    if args[:1] == ["--expect-open"]:
        lo, _, hi = args[1].partition("-")
        lo, hi = int(lo), int(hi or lo)
        line = args[1]
        regex, spec = re.compile(args[2]), args[3]
        goals = load(spec)
        if goals is None:
            return 1
        open_goals = census(goals)
        wrong = [g for g in open_goals
                 if not lo <= (g["line"] or 0) <= hi
                 or not regex.search(g["goal"])]
        if not open_goals:
            print(f"expected an open goal on line {line}; all proved")
            return 1
        if wrong:
            print(f"open goals other than /{regex.pattern}/ on line {line}:")
            for g in wrong:
                print(f"  {g['goal']} (line {g['line']})")
            return 1
        return 0
    loaded = [load(spec) for spec in args]
    if not loaded or any(g is None for g in loaded):
        return 1
    return 1 if census([g for gs in loaded for g in gs]) else 0


if __name__ == "__main__":
    sys.exit(main())
