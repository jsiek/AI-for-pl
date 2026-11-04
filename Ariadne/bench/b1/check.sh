#!/bin/sh
# B1a check.  From this directory:  ./check.sh
#   1. ./run.sh: every goal of b1.c (functions and lemmas) is proved.
#   2. Mutants of the driver, each of which must leave exactly its
#      intended goal(s) unproved, on the intended line, and nothing else:
#      vacuity  - `assert \false` at the end of b1 (else the spec is
#                 inconsistent and step 1 means nothing);
#      uaf      - the walks (get_first forward, get_last backward)
#                 moved after the free loop;
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

# The two walks (from get_first forward, from get_last backward), with
# the assert in front of them.
i = src.index("  /*@ assert head_is_node0:")
tail = "       l = l->ptr_to_previous)\n    last = l->i;\n"
walks_end = src.index(tail, i) + len(tail)
walk = src[i:walks_end]
mutant("vacuity", "  return last;\n}",
       "  //@ assert vacuity: \\false;\n  return last;\n}")
free_loop_end = "            all_live{before_free}(s) && !mem(l, s) ==> all_live(s); */\n  }\n"
j = src.index(free_loop_end) + len(free_loop_end)
uaf = src[:i] + src[walks_end:j] + walk + src[j:]
open("mutants/uaf.c", "w").write(uaf)
mutant("nullchk", "    if (l == NULL)\n      break;\n", "")
EOF

# The intended failure of each mutant: a unique line of the mutant
# source (found by its text) and a pattern for the open goal names there.
expect() {
  case "$1" in
    vacuity) marker='  //@ assert vacuity: \false;'
             goals='_assert_vacuity$' ;;
    uaf)     marker='        the_list == \null'  # head_is_node0's first line
             goals='_assert_head_is_node0$' ;;
    nullchk) marker='    l->i = input[k];'
             goals='_assert_(ariadne_live|rte_mem_access)(_[0-9]+)?$' ;;
  esac
}

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
  expect "$m"
  line=$(grep -nF -- "$marker" "mutants/$m.c" | cut -d: -f1)
  if [ "$(echo "$line" | wc -w)" -ne 1 ]; then
    echo "FAIL: mutant $m: marker not found exactly once"; status=1
  elif [ ! -s "mutants/report_$m.json" ]; then
    echo "FAIL: mutant $m: WP run failed (mutants/$m.log)"; status=1
  elif python3 -I ../goals.py --expect-open "$line" "$goals" \
         "mutants/report_$m.json" > "mutants/$m.goals"; then
    echo "PASS: mutant $m rejected, only at line $line: $(sed -n 2p \
      "mutants/$m.goals" | awk '{print $2}')"
  else
    echo "FAIL: mutant $m not rejected for the intended reason:"
    sed 's/^/    /' "mutants/$m.goals"; status=1
  fi
done
exit $status
