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
#      nowashead - add's contract without was_head: the driver cannot
#                 tell that the new node is the head (head_after_add);
#      noassign - elem->previous dropped from add's assigns: add's assigns
#                 clause fails;
#      noinit   - the driver does not store input[k] into the new node
#                 (`l->i = input[k];` removed), so the walks would read an
#                 uninitialised field: the driver's assert payload_written fails.
set -u
status=0

if ./run.sh; then
  echo "PASS: b1.c fully proved"
else
  echo "FAIL: b1.c not fully proved"; status=1
fi

rm -rf mutants
python3 -I mutants.py b1.c mutants   # shared with rac/check.sh

# The intended failure of each mutant: a unique line of the mutant
# source (found by its text) and a pattern for the open goal names there.
expect() {
  fct=b1 span=0
  case "$1" in
    vacuity) marker='  //@ assert vacuity: \false;'
             goals='_assert_vacuity$' ;;
    uaf)     marker='  for (l = sglib_dllist_get_first(the_list); l != NULL; l = l->ptr_to_next)'
             goals='_call_sglib_dllist_get_first_requires(_[0-9]+)?$' ;;
    uaf_back) marker='  for (l = sglib_dllist_get_last(the_list); l != NULL;'
             goals='_call_sglib_dllist_get_last_requires(_[0-9]+)?$' ;;
    nullchk) marker='    l->i = input[k];'
             # and payload_kept after the add (the provers do not find
             # the contradiction of a NULL l assumed valid there)
             span=13 goals='_assert_(ariadne_live|rte_mem_access(_[0-9]+)?|payload_kept)$' ;;
    nullfirst) marker='/*@ SGLIB_DL_LIST_CONTRACT_GET_FIRST(dllist, ptr_to_previous, ptr_to_next) */'
             goals='_ensures_heads_list$' fct=sglib_dllist_get_first ;;
    nulllast) marker='/*@ SGLIB_DL_LIST_CONTRACT_GET_LAST(dllist, ptr_to_previous, ptr_to_next) */'
             goals='_ensures_last_of_list$' fct=sglib_dllist_get_last ;;
    noinit)  marker='    /*@ assert payload_written:'
             span=6   # payload_written, and payload_kept after the add
             goals='_assert_payload_(written|kept)$' ;;
    nowashead) marker='    /*@ assert head_after_add:'
             span=1 goals='_assert_head_after_add$' ;;
    noassign) marker='/*@ SGLIB_DL_LIST_CONTRACT_ADD(dllist, ptr_to_previous, ptr_to_next) */'
             goals='_assigns' fct=sglib_dllist_add ;;
  esac
}

for m in vacuity uaf uaf_back nullchk nullfirst nulllast noinit nowashead noassign; do
  rm -f "mutants/report_$m.json"
  rm -rf "mutants/session_$m" && mkdir -p "mutants/session_$m"
  cp -r session/interactive "mutants/session_$m/"   # the Coq scripts
  expect "$m"
  ../../env/run.sh frama-c \
    -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
    -cpp-extra-args="-I/ariadne/plugin/share -I/ariadne/bench/sglib_spec" \
    -generated-spec-custom terminates:skip \
    -ariadne "mutants/$m.c" \
    -then -wp -wp-rte -rte-initialized @all -wp-no-filter-init \
    -wp-model Typed -wp-fct "$fct" \
    -wp-prover alt-ergo,z3,cvc5,coq -wp-interactive batch -wp-timeout 60 \
    -wp-session "/work/mutants/session_$m" \
    -wp-report-json "/work/mutants/report_$m.json" \
    > "mutants/$m.log" 2>&1
  line=$(grep -nF -- "$marker" "mutants/$m.c" | cut -d: -f1)
  if [ "$(echo "$line" | wc -w)" -ne 1 ]; then
    echo "FAIL: mutant $m: marker not found exactly once"; status=1
  elif [ ! -s "mutants/report_$m.json" ]; then
    echo "FAIL: mutant $m: WP run failed (mutants/$m.log)"; status=1
  elif python3 -I ../goals.py --expect-open "$line-$((line + span))" "$goals" \
         "mutants/report_$m.json" > "mutants/$m.goals"; then
    echo "PASS: mutant $m rejected, only at line $line: $(sed -n 2p \
      "mutants/$m.goals" | awk '{print $2}')"
  else
    echo "FAIL: mutant $m not rejected for the intended reason:"
    sed 's/^/    /' "mutants/$m.goals"; status=1
  fi
done
exit $status
