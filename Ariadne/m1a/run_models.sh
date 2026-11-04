#!/bin/sh
# M1a: run WP on a test file under each memory model; one JSON report each.
#   usage: [SRC=file.c] ./run_models.sh [model ...]
#   (default: alloc.c, all models below)
# Exits non-zero if any run fails or leaves no report, so a stale report
# from an earlier run can never be scored as fresh.
set -u
src="${SRC:-alloc.c}"
name=$(basename "$src" .c)
models="${*:-Typed Typed+cast Bytes Region Eva}"
status=0
for m in $models; do
  tag="${name}_$(echo "$m" | tr '+' '_')"
  report="report_$tag.json"
  rm -f "$report"
  extra=""
  [ "$m" = "Eva" ] && extra="-eva -then"
  # shellcheck disable=SC2086
  ../env/run.sh frama-c $extra -wp -wp-rte -wp-model "$m" \
    -wp-prover alt-ergo,z3,cvc5 -wp-timeout 10 \
    -wp-session "/work/session_$tag" \
    -wp-report-json "/work/$report" \
    "$src" > "run_$tag.log" 2>&1
  rc=$?
  echo "== $m: exit $rc, $(grep -c 'not yet implemented' "run_$tag.log")" \
    "'not yet implemented' warnings; $(grep -E 'Proved goals' "run_$tag.log")"
  if [ "$rc" -ne 0 ] || [ ! -s "$report" ]; then
    echo "   run failed or wrote no report; see run_$tag.log" >&2
    status=1
  fi
done
exit $status
