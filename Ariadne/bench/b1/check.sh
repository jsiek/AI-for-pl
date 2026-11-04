#!/bin/sh
# B1a check.  From this directory:  ./check.sh
#   1. ./run.sh: every goal of b1.c (functions and lemmas) is proved.
#   2. Mutants of the driver, each of which must leave a goal unproved:
#      vacuity  - `assert \false` at the end of b1 (else the spec is
#                 inconsistent and step 1 means nothing);
#      uaf      - the forward walk moved after the free loop;
#      nullchk  - the NULL check after allocation removed (as in the
#                 original sglib sample).
set -u
status=0

if ./run.sh; then
  echo "PASS: b1.c fully proved"
else
  echo "FAIL: b1.c not fully proved"; status=1
fi

rm -rf mutants && mkdir mutants
python3 -I - <<'EOF'
src = open("b1.c").read()

def mutant(name, old, new):
    assert src.count(old) == 1, (name, old)
    open(f"mutants/{name}.c", "w").write(src.replace(old, new))

walk = """  /*@ loop invariant \\exists dllist *p, \\list<dllist *> t; live_dll(p, l, t);
      loop assigns l, last;
  */
  for (l = the_list; l != NULL; l = l->ptr_to_next)
    last = l->i;
"""
mutant("vacuity", "  return last;\n}",
       "  //@ assert vacuity: \\false;\n  return last;\n}")
free_loop_end = "            all_live{before_free}(s) && !mem(l, s) ==> all_live(s); */\n  }\n"
i = src.index(walk)
j = src.index(free_loop_end) + len(free_loop_end)
uaf = src[:i] + src[i + len(walk):j] + walk + src[j:]
open("mutants/uaf.c", "w").write(uaf)
mutant("nullchk", "    if (l == NULL)\n      break;\n", "")
EOF

for m in vacuity uaf nullchk; do
  rm -f "mutants/report_$m.json"
  ../../env/run.sh frama-c \
    -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
    -cpp-extra-args="-I/ariadne/plugin/share" \
    -generated-spec-custom terminates:skip \
    -ariadne "mutants/$m.c" \
    -then -wp -wp-rte -wp-model Typed -wp-fct b1 \
    -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
    -wp-session "/work/mutants/session_$m" \
    -wp-report-json "/work/mutants/report_$m.json" \
    > "mutants/$m.log" 2>&1
  if [ ! -s "mutants/report_$m.json" ]; then
    echo "FAIL: mutant $m: WP run failed (mutants/$m.log)"; status=1
  elif python3 -I ../goals.py "mutants/report_$m.json" > "mutants/$m.goals"
  then
    echo "FAIL: mutant $m fully proved (should not be)"; status=1
  else
    echo "PASS: mutant $m rejected: $(sed -n 2p "mutants/$m.goals" \
      | awk '{print $2}')"
  fi
done
exit $status
