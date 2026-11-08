#!/bin/sh
# WP on the step-0 reference b1a_ref.c (B1's human-annotated b1.c with
# B1a's driver), on B1a's selection (the four sglib functions and b1)
# and the lemmas, with B1's Coq scripts (../b1/session/interactive), and
# the same flags as ../b1/run.sh.  From this directory:  ./run_ref.sh
# Prints the census; exits 0 only if every goal is proved.
set -u
rm -rf ref_session && mkdir -p ref_session
cp -r ../b1/session/interactive ref_session/
fcts="sglib_dllist_add,sglib_dllist_it_init_on_equal,sglib_dllist_it_init"
fcts="$fcts,sglib_dllist_it_next,b1"
status=0
wp() {  # wp <report> <log> <WP selection options...>
  report=$1 log=$2; shift 2
  rm -f "$report"
  ../../env/run.sh frama-c \
    -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
    -cpp-extra-args="-I/ariadne/plugin/share -I/ariadne/bench/b1a/spec_full" \
    -generated-spec-custom terminates:skip \
    -ariadne b1a_ref.c \
    -then -wp -wp-model Typed -wp-no-filter-init "$@" \
    -wp-prover alt-ergo,z3,cvc5,coq -wp-interactive batch -wp-timeout 60 \
    -wp-session /work/ref_session -wp-report-json "/work/$report" \
    > "$log" 2>&1 || status=1
  [ -s "$report" ] || { echo "WP run failed; see $log"; status=1; }
}
wp ref_fct.json ref_fct.log -wp-rte -rte-initialized @all -wp-fct "$fcts"
wp ref_lemmas.json ref_lemmas.log -wp-prop=@lemma
[ "$status" -eq 0 ] || exit 1
python3 -I ../goals.py ref_fct.json ref_lemmas.json
