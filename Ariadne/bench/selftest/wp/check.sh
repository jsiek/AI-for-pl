#!/bin/sh
# The self-test instance (st_wp.c): ./run.sh (every goal proved), then
# two mutants of our driver st_iter_equal, each of which must leave open
# only the intended call precondition, on the for line (or the line
# after, where it_next is called):
#   othercmp  - a second comparator otherCmp, outside the allowed set
#               (1, myListCmp), is passed as subcomparator: the set
#               membership precondition fails;
#   noeqinit  - the driver no longer requires te->n initialised:
#               it_init_on_equal's cmp_reads(equalto) fails.
#   From this directory:  ./check.sh
set -u
status=0
python3 -I gen_wp.py || exit 1
if ./run.sh; then echo "PASS: st_wp.c fully proved"; else
  echo "FAIL: st_wp.c not fully proved"; status=1; fi
rm -rf mutants && mkdir -p mutants
python3 -I - <<'EOF'
s = open("st_wp.c").read()
def write(name, pairs):
    t = s
    for a, b in pairs:
        assert t.count(a) == 1, (name, a)
        t = t.replace(a, b)
    open(f"mutants/{name}.c", "w").write(t)
other = ("/*@ SGLIB_DL_LIST_CONTRACT_COMPARATOR(DoubleLinkedList, st_cmp_reads,"
         "\n                                      a, b) */\n"
         "int otherCmp(struct MyIntList *a, struct MyIntList *b) {\n"
         "  return (a->n < b->n) - (a->n > b->n);\n}\n\n")
write("othercmp", [
    ("/* Our driver (not sglib's)", other + "/* Our driver (not sglib's)"),
    ("it->subcomparator == &myListCmp;", "it->subcomparator == &otherCmp;"),
    ("(it, list, myListCmp, te)", "(it, list, otherCmp, te)")])
write("noeqinit", [("    requires te_init: \\initialized(&te->n);\n", "")])
EOF
for m in othercmp noeqinit; do
  rm -rf "mutants/session_$m"; mkdir -p "mutants/session_$m"
  cp -r session/interactive "mutants/session_$m/"
  ../../../env/run.sh frama-c \
    -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
    -cpp-extra-args="-I/ariadne/plugin/share -I/ariadne/bench/sglib_spec" \
    -generated-spec-custom terminates:skip -ariadne "mutants/$m.c" \
    -then -wp -wp-rte -rte-initialized @all -wp-no-filter-init \
    -wp-model Typed -wp-fct st_iter_equal \
    -wp-prover alt-ergo,z3,cvc5,coq -wp-interactive batch -wp-timeout 60 \
    -wp-session "/work/mutants/session_$m" \
    -wp-report-json "/work/mutants/report_$m.json" > "mutants/$m.log" 2>&1
  line=$(grep -n "  for (ll = sglib_DoubleLinkedList_it_init_on_equal" \
           "mutants/$m.c" | cut -d: -f1)
  if python3 -I ../../goals.py --expect-open "$line-$((line + 1))" \
       '_call_sglib_DoubleLinkedList_it_(init_on_equal|next)_requires(_[0-9]+)?$' \
       "mutants/report_$m.json" > "mutants/$m.goals"; then
    echo "PASS: mutant $m rejected, only at the iterator calls (lines $line-$((line + 1))): $(sed -n '2,3p' "mutants/$m.goals" | awk '{print $2}' | tr '\n' ' ')"
  else
    echo "FAIL: mutant $m:"; sed 's/^/    /' "mutants/$m.goals"; status=1
  fi
done
exit $status
