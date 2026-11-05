#!/bin/sh
# Does WP 33 prove calls through a function pointer with `calls`?
# (owner decision 3, 2026-11-05; README.md, "Subcomparator: stopped")
#   call_statement.c         the indirect call is a statement:
#                            `/*@ calls cmp1, cmp2; */ r = f(x, y);`
#   call_in_loop_condition.c the indirect call is in a while condition,
#                            as in sglib's it_next:
#                            `while (ce != 0 && f(x, ce) != 0) ...`
# Prints WP's goals for each.
set -u
for f in call_statement call_in_loop_condition; do
  echo "== $f.c"
  ../../../env/run.sh frama-c "$f.c" -generated-spec-custom terminates:skip \
    -wp -wp-rte -rte-initialized @all -wp-no-filter-init \
    -wp-prover alt-ergo,z3,cvc5 -wp-timeout 10 -wp-cache none \
    -wp-report-json "/work/$f.json" 2>&1 \
    | grep -E "Missing 'calls'|Proved goals"
  python3 -c 'import json, sys
for g in json.load(open(sys.argv[1])):
    if "call" in g["goal"] or g["verdict"] != "valid":
        print("  ", g["goal"], g["verdict"])' "$f.json"
  rm -f "$f.json"
done
