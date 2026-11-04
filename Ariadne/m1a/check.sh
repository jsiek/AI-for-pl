#!/bin/sh
# M1a check.  Run from this directory:  ./check.sh
#   1. alloc.c (Frama-C libc malloc/free) under Typed and Bytes: expected
#      to be WRONG (use-after-free proved safe); this step passes while
#      WP still lacks allocation support, so we notice if that changes.
#   2. ghost.c (ghost liveness model) under Typed: every case correct.
set -u
status=0

./run_models.sh Typed Bytes
for m in Typed Bytes; do
  if python3 -I summarize.py alloc.c "report_alloc_$m.json" \
       | grep -q "UNSOUND"; then
    echo "PASS: WP $m still misses use-after-free with libc specs"
  else
    echo "FAIL: WP $m no longer misses use-after-free; revisit plan §10"
    status=1
  fi
done

SRC=ghost.c ./run_models.sh Typed
if python3 -I summarize.py ghost.c report_ghost_Typed.json; then
  echo "PASS: ghost liveness model, every case correct"
else
  echo "FAIL: ghost liveness model"
  status=1
fi
exit $status
