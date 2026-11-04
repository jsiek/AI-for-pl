#!/bin/sh
# M1a: run WP on alloc.c under each memory model; one JSON report each.
#   usage: [SRC=file.c] ./run_models.sh [model ...]
#   (default: alloc.c, all models below)
set -u
src="${SRC:-alloc.c}"
name=$(basename "$src" .c)
models="${*:-Typed Typed+cast Bytes Region Eva}"
for m in $models; do
  tag="${name}_$(echo "$m" | tr '+' '_')"
  extra=""
  [ "$m" = "Eva" ] && extra="-eva -then"
  # shellcheck disable=SC2086
  ../env/run.sh frama-c $extra -wp -wp-rte -wp-model "$m" \
    -wp-prover alt-ergo,z3,cvc5 -wp-timeout 10 \
    -wp-session "/work/session_$tag" \
    -wp-report-json "/work/report_$tag.json" \
    "$src" > "run_$tag.log" 2>&1
  echo "== $m: exit $?, $(grep -c 'not yet implemented' "run_$tag.log")" \
    "'not yet implemented' warnings; $(grep -E 'Proved goals' "run_$tag.log")"
done
