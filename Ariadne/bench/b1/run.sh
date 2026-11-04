#!/bin/sh
# Verify benchmark B1a: -ariadne + WP on b1.c, in two passes,
#   1. the B1a functions (sglib add / iterator, and the driver b1);
#   2. the lemmas of the spec (Coq scripts in session/interactive);
# then print the goal census and any goal not proved.
#   From this directory:  ./run.sh [extra WP options]
# Needs the plugin built (../../plugin: ../env/run.sh dune build).
# Termination is a plan non-goal (section 1.4): terminates clauses are
# not generated, so no termination goals are created.
set -u
fcts="sglib_dllist_add,sglib_dllist_it_init_on_equal,sglib_dllist_it_init"
fcts="$fcts,sglib_dllist_it_next,sglib_dllist_get_first,sglib_dllist_get_last,b1"
extra="$*"
status=0

wp() {  # wp <report> <log> <WP selection options...>
  report=$1 log=$2; shift 2
  rm -f "$report"
  # shellcheck disable=SC2086
  ../../env/run.sh frama-c \
    -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
    -cpp-extra-args="-I/ariadne/plugin/share" \
    -generated-spec-custom terminates:skip \
    -ariadne b1.c \
    -then -wp -wp-model Typed "$@" \
    -wp-prover alt-ergo,z3,cvc5,coq -wp-interactive batch -wp-timeout 60 \
    -wp-session /work/session -wp-report-json "/work/$report" $extra \
    > "$log" 2>&1
  rc=$?
  grep -E "\[ariadne\]|Proved goals|User Error|aborted" "$log"
  if [ "$rc" -ne 0 ] || [ ! -s "$report" ]; then
    echo "WP run failed (exit $rc); see $log"; status=1
  fi
}

wp report_fct.json run_fct.log -wp-rte -wp-fct "$fcts"
wp report_lemmas.json run_lemmas.log -wp-prop=@lemma
[ "$status" -eq 0 ] || exit 1
# Exact goal counts, so a selection that silently shrinks cannot pass.
python3 -I ../goals.py report_fct.json:212 report_lemmas.json:8
