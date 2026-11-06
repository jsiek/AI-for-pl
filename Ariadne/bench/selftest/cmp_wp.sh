#!/bin/sh
# The comparator rule (../sglib_spec/README.md): selftest's comparator
# myListCmp is proved free of runtime errors under the template's
# comparator contract, SGLIB_DL_LIST_CONTRACT_COMPARATOR(DoubleLinkedList,
# st_cmp_reads, e1, e2) in selftest_dl.c: -ariadne (liveness asserts),
# then WP with -wp-rte -rte-initialized @all, Alt-Ergo, Z3, CVC5.
# ST_WP_ONLY leaves out the allocator bodies, whose raw malloc/free
# -ariadne refuses.  Exit 0 iff every goal of myListCmp is proved.
set -u
../../env/run.sh frama-c \
  -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
  -cpp-extra-args="-DST_WP_ONLY -I/ariadne/plugin/share -I/ariadne/bench/sglib_spec -I/ariadne/bench/sglib -I/ariadne/rac" \
  -generated-spec-custom terminates:skip -ariadne selftest_dl.c \
  -then -wp -wp-rte -rte-initialized @all -wp-no-filter-init \
  -wp-fct myListCmp -wp-prover alt-ergo,z3,cvc5 -wp-timeout 30 \
  -wp-cache none -wp-report-json /work/cmp_wp.json > cmp_wp.log 2>&1
python3 -I ../goals.py cmp_wp.json
