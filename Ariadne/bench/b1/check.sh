#!/bin/sh
# B1a check.  From this directory:  ./check.sh
#   1. ./run.sh: every goal of b1.c (functions and lemmas) is proved.
#   2. Mutants of the driver, each of which must leave exactly its
#      intended goal(s) unproved, on the intended line, and nothing else:
#      vacuity  - `assert \false` at the end of b1 (else the spec is
#                 inconsistent and step 1 means nothing);
#      uaf      - the forward walk (from get_first) moved after the
#                 free loop;
#      uaf_back - the backward walk (from get_last) moved after the
#                 free loop;
#      nullchk  - the NULL check after allocation removed (as in the
#                 original sglib sample);
#      nullfirst, nulllast - get_first / get_last return NULL after the
#                 traversal (their contracts must tie the result to the
#                 input's list, so this must fail);
#      noinit   - the driver does not store input[k] into the new node
#                 (`l->i = input[k];` removed), so the walks would read an
#                 uninitialised field: add's precondition elem_init fails.
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

# The forward walk (the loop after the head_is_node0 assert, which stays
# in place for the backward walk) and the backward walk, each moved after
# the free loop in its own mutant.
assert_start = src.index("  /*@ assert head_is_node0:")
assert_end = "             live_dll(\\null, the_list, \\Cons(the_list, t)); */\n"
fwd_start = src.index(assert_end, assert_start) + len(assert_end)
back_start = src.index("  /*@ loop invariant l == \\null || in_live_list(l);")
tail = "       l = l->ptr_to_previous)\n    last = l->i;\n"
back_end = src.index(tail, back_start) + len(tail)
mutant("vacuity", "  return last;\n}",
       "  //@ assert vacuity: \\false;\n  return last;\n}")
free_loop_end = ("            live_dll{before_free}(p, h, s) && !mem(l, s)"
                 " ==> live_dll(p, h, s); */\n  }\n")
j = src.index(free_loop_end) + len(free_loop_end)

def move_after_free(name, a, b):
    out = src[:a] + src[b:j] + src[a:b] + src[j:]
    open(f"mutants/{name}.c", "w").write(out)

move_after_free("uaf", fwd_start, back_start)
move_after_free("uaf_back", back_start, back_end)
mutant("nullchk", "    if (l == NULL)\n      break;\n", "")

def null_result(name, fun):
    i = src.index(f"dllist *{fun}(dllist *list) {{")
    j = src.index("    (result) = _dll_;", i)
    out = src[:j] + "    (result) = NULL;" + src[j + len("    (result) = _dll_;"):]
    open(f"mutants/{name}.c", "w").write(out)

null_result("nullfirst", "sglib_dllist_get_first")
null_result("nulllast", "sglib_dllist_get_last")
mutant("noinit", "    l->i = input[k];\n", "")
EOF

# The intended failure of each mutant: a unique line of the mutant
# source (found by its text) and a pattern for the open goal names there.
expect() {
  fct=b1
  case "$1" in
    vacuity) marker='  //@ assert vacuity: \false;'
             goals='_assert_vacuity$' ;;
    uaf)     marker='  for (l = sglib_dllist_get_first(the_list); l != NULL; l = l->ptr_to_next)'
             goals='_call_sglib_dllist_get_first_requires(_[0-9]+)?$' ;;
    uaf_back) marker='  for (l = sglib_dllist_get_last(the_list); l != NULL;'
             goals='_call_sglib_dllist_get_last_requires(_[0-9]+)?$' ;;
    nullchk) marker='    l->i = input[k];'
             goals='_assert_(ariadne_live|rte_mem_access)(_[0-9]+)?$' ;;
    nullfirst) marker='    ensures heads_list: list != \null ==>'
             goals='_ensures_heads_list$' fct=sglib_dllist_get_first ;;
    nulllast) marker='    ensures last_of_list: list != \null ==>'
             goals='_ensures_last_of_list$' fct=sglib_dllist_get_last ;;
    noinit)  marker='    sglib_dllist_add(&the_list, l);'
             goals='_call_sglib_dllist_add_requires_elem_init$' ;;
  esac
}

for m in vacuity uaf uaf_back nullchk nullfirst nulllast noinit; do
  rm -f "mutants/report_$m.json"
  expect "$m"
  ../../env/run.sh frama-c \
    -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
    -cpp-extra-args="-I/ariadne/plugin/share" \
    -generated-spec-custom terminates:skip \
    -ariadne "mutants/$m.c" \
    -then -wp -wp-rte -rte-initialized @all -wp-no-filter-init \
    -wp-model Typed -wp-fct "$fct" \
    -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
    -wp-session "/work/mutants/session_$m" \
    -wp-report-json "/work/mutants/report_$m.json" \
    > "mutants/$m.log" 2>&1
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
