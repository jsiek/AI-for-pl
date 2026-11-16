#!/bin/sh
# Plugin test.  Run from Ariadne/plugin:  tests/check.sh
#   1. build the plugin;
#   2. reject raw malloc/free (tests/raw_malloc.c must be refused);
#   3. instrument tests/uaf.c with -ariadne, run WP, and score every test
#      function (good proved, bad caught on its BAD line, vacuity not
#      proved) with m1a/summarize.py --any.
set -u
run=../env/run.sh
status=0
fc="frama-c -load-module _build/default/ariadne.cmxs -cpp-extra-args=-Ishare"

if "$run" env DUNE_CACHE=disabled dune build; then
  echo "PASS: plugin builds"
else
  echo "FAIL: plugin does not build"; exit 1
fi

if $run $fc -ariadne tests/raw_malloc.c > tests/raw_malloc.log 2>&1; then
  echo "FAIL: raw malloc/free was accepted"; status=1
elif [ "$(grep -c "use of \(malloc\|free\)" tests/raw_malloc.log)" -eq 4 ]
then
  echo "PASS: raw malloc/free rejected (direct calls and function pointers)"
else
  echo "FAIL: raw_malloc.c rejected for another reason (tests/raw_malloc.log)"
  status=1
fi

rm -f tests/report_uaf.json
if ! $run $fc -ariadne tests/uaf.c -then -wp -wp-rte -wp-model Typed \
     -wp-prover alt-ergo,z3,cvc5 -wp-timeout 10 \
     -wp-session /work/tests/session_uaf \
     -wp-report-json /work/tests/report_uaf.json > tests/uaf.log 2>&1 \
   || [ ! -s tests/report_uaf.json ]; then
  echo "FAIL: -ariadne + WP run on uaf.c (tests/uaf.log)"; exit 1
fi
grep -E "\[ariadne\]|Proved goals" tests/uaf.log
if python3 -I ../m1a/summarize.py --any tests/uaf.c tests/report_uaf.json; then
  echo "PASS: every uaf.c case correct"
else
  echo "FAIL: uaf.c (see above and tests/uaf.log)"; status=1
fi
exit $status
