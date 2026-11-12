#!/bin/sh
# WP on drop_list.c (an add that drops the caller's list) under add's
# public contract of 2026-11-08 (must prove: the old spec accepts it) and
# under today's (must leave in_old_list open: the new spec rejects it).
# From this directory:  ./run.sh     (needs the M0 image and the plugin)
set -u
status=0
wp() {  # wp <name> <include dir>
  rm -f "report_$1.json"
  ../../../env/run.sh frama-c \
    -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
    -cpp-extra-args="-I/ariadne/plugin/share -I$2" \
    -generated-spec-custom terminates:skip -ariadne drop_list.c \
    -then -wp -wp-model Typed -wp-no-filter-init -wp-rte \
    -rte-initialized @all -wp-fct sglib_dllist_add \
    -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
    -wp-report-json "/work/report_$1.json" > "$1.log" 2>&1
  python3 -c 'import json, sys
g = json.load(open(sys.argv[1]))
bad = [x["goal"] for x in g if x["verdict"] != "valid"]
print(len(g) - len(bad), "/", len(g), "proved; open:", bad)' "report_$1.json"
}
old=$(wp old /ariadne/bench/sglib_spec/anchor_probe/spec_2026-11-08)
new=$(wp new /ariadne/bench/sglib_spec)
echo "spec of 2026-11-08: $old"
echo "spec with in_old_list: $new"
case "$old" in *"open: []"*) echo "PASS: the old spec accepts droplist" ;;
  *) echo "FAIL: the old spec does not accept droplist"; status=1 ;; esac
case "$new" in *in_old_list*) echo "PASS: the new spec rejects droplist at in_old_list" ;;
  *) echo "FAIL: the new spec does not reject droplist at in_old_list"; status=1 ;; esac
exit $status
