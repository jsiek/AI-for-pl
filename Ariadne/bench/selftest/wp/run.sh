#!/bin/sh
# WP on st_wp.c (gen_wp.py): the six specified sglib functions, the
# comparator myListCmp and our driver st_iter_equal, then the lemmas, as
# ../../b1/run.sh does for B1.  The Coq scripts are B1's
# (../../b1/session/interactive), copied into session/ under this
# instance's goal names.
#   From this directory:  ./run.sh [extra WP options]
set -u
fcts="sglib_DoubleLinkedList_add,sglib_DoubleLinkedList_get_first"
fcts="$fcts,sglib_DoubleLinkedList_get_last"
fcts="$fcts,sglib_DoubleLinkedList_it_init_on_equal"
fcts="$fcts,sglib_DoubleLinkedList_it_init,sglib_DoubleLinkedList_it_next"
fcts="$fcts,myListCmp,st_iter_equal"
extra="$*"
status=0
mkdir -p session/interactive
for f in ../../b1/session/interactive/*.v; do
  b=$(basename "$f" | sed 's/sglib_dllist_/sglib_DoubleLinkedList_/')
  [ -e "session/interactive/$b" ] || cp "$f" "session/interactive/$b"
done
wp() {  # wp <report> <log> <WP selection options...>
  report=$1 log=$2; shift 2
  rm -f "$report"
  # shellcheck disable=SC2086
  ../../../env/run.sh frama-c \
    -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
    -cpp-extra-args="-I/ariadne/plugin/share -I/ariadne/bench/sglib_spec" \
    -generated-spec-custom terminates:skip \
    -ariadne st_wp.c \
    -then -wp -wp-model Typed -wp-no-filter-init "$@" \
    -wp-prover alt-ergo,z3,cvc5,coq -wp-interactive batch -wp-timeout 60 \
    -wp-session /work/session -wp-report-json "/work/$report" $extra \
    > "$log" 2>&1
  rc=$?
  grep -E "\[ariadne\]|Proved goals|User Error|aborted" "$log"
  if [ "$rc" -ne 0 ] || [ ! -s "$report" ]; then
    echo "WP run failed (exit $rc); see $log"; status=1
  fi
}
wp report_fct.json run_fct.log -wp-rte -rte-initialized @all -wp-fct "$fcts"
wp report_lemmas.json run_lemmas.log -wp-prop=@lemma
[ "$status" -eq 0 ] || exit 1
python3 -I ../../goals.py report_fct.json report_lemmas.json
