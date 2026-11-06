"""Step 0's per-clause coverage report (plan Q11).

   usage: python3 -I coverage.py MAP.json ANNOTATIONS.txt OUT.md \\
              LABEL=COUNTS.tsv [LABEL=COUNTS.tsv ...]

MAP.json and ANNOTATIONS.txt come from gen_rac.py --cov; each COUNTS.tsv
from the COV lines a run with rac_collect.c prints, labelled by its
input (the target's tests, operation sequences, a driver).  The report:

- every clause that is checked at run time (`rac_cov_<n>`): how often it
  was evaluated in each input and in all, how often it failed, and for
  each side of a top-level implication (the antecedent) or disjunction
  (each disjunct, as the first one that holds) how often that side held;
- flags: a clause never evaluated on any input; an implication whose
  antecedent never held (only vacuously true); a disjunct never the one
  that held;
- the clauses not checked at run time, with gen_rac.py's reason.

Prints one summary line; exit status 0 (a filter's report, not a
verdict)."""
import collections
import json
import re
import sys

cmap = json.load(open(sys.argv[1]))
ann = open(sys.argv[2]).read().splitlines()
out = sys.argv[3]
runs = [a.split("=", 1) for a in sys.argv[4:]]

evals = collections.defaultdict(lambda: collections.Counter())
fails = collections.Counter()
side_true = collections.Counter()
for label, path in runs:
    try:
        lines = open(path).read().splitlines()
    except OSError:
        lines = []
    for ln in lines:
        parts = ln.split("\t")
        if len(parts) != 6:
            continue
        _, name, _, _, t, f = parts
        m = re.search(r"rac_side_(\d+)_(\d+)", name)
        if m:
            side_true[(int(m.group(1)), int(m.group(2)))] += int(t)
            continue
        m = re.search(r"rac_cov_(\d+)", name)
        if m:
            n = int(m.group(1))
            evals[n][label] += int(t) + int(f)
            fails[n] += int(f)

labels = [label for label, _ in runs]
rows, flags = [], []
for c in cmap:
    n = c["n"]
    tot = sum(evals[n].values())
    sides = "; ".join(f"{s['role']}: {side_true[(n, s['j'])]}"
                      for s in c["sides"]) or "-"
    rows.append(f"| {c['where']} | {c['label']} | "
                + " | ".join(str(evals[n][x]) for x in labels)
                + f" | {tot} | {fails[n]} | {sides} |")
    if tot == 0:
        flags.append(f"never evaluated: {c['where']} {c['label']}")
    for s in c["sides"]:
        if tot and side_true[(n, s["j"])] == 0:
            what = ("antecedent never held (only vacuously true)"
                    if s["role"] == "antecedent"
                    else f"{s['role']} never the one that held")
            flags.append(f"{what}: {c['where']} {c['label']}")
dropped = [ln for ln in ann if ": dropped (" in ln
           or ": partly-kept (" in ln]
with open(out, "w") as f:
    f.write("# Step-0 clause coverage\n\n")
    f.write("Inputs: " + ", ".join(f"`{x}`" for x in labels) + ".\n\n")
    f.write("| Clause | Kind and name | " + " | ".join(labels)
            + " | all | failed | sides held |\n")
    f.write("|---|---|" + "---|" * len(labels) + "---|---|---|\n")
    f.write("\n".join(rows) + "\n\n")
    f.write(f"## Flags ({len(flags)})\n\n")
    f.write("".join(f"- {x}\n" for x in flags) or "none\n")
    f.write(f"\n## Not checked at run time ({len(dropped)})\n\n")
    f.write("".join(f"- {x}\n" for x in dropped) or "none\n")
never = sum(1 for x in flags if x.startswith("never evaluated"))
print(f"coverage: {len(cmap)} clauses checked at run time, "
      f"{len(cmap) - never} evaluated, {never} never evaluated, "
      f"{len(flags) - never} side flags, {sum(fails.values())} failures; "
      f"{len(dropped)} clauses not (or only partly) checked at run time")
