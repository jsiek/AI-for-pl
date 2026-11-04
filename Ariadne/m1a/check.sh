#!/bin/sh
# M1a check.  Run from this directory:  ./check.sh
#   1. alloc.c (Frama-C libc malloc/free) under Typed and Bytes: the
#      per-function verdicts must equal expected_libc.txt exactly (WP
#      proves some use-after-free reads safe).  Any change, better or
#      worse, fails, so we notice when WP's allocation support changes.
#   2. ghost.c (ghost liveness model) under Typed: every case correct.
# A failed or missing WP run fails the check; reports are never reused.
set -u
status=0

if ! ./run_models.sh Typed Bytes; then
  echo "FAIL: WP run on alloc.c"; exit 1
fi
for m in Typed Bytes; do
  python3 -I summarize.py alloc.c "report_alloc_$m.json" \
    | grep -E '^  [a-z_]+ +[A-Za-z]' > "verdicts_$m.txt"
  if diff -u expected_libc.txt "verdicts_$m.txt"; then
    echo "PASS: WP $m with libc specs matches the recorded baseline"
  else
    echo "FAIL: WP $m with libc specs changed; revisit plan §10"
    status=1
  fi
done

if ! SRC=ghost.c ./run_models.sh Typed; then
  echo "FAIL: WP run on ghost.c"; exit 1
fi
if python3 -I summarize.py ghost.c report_ghost_Typed.json; then
  echo "PASS: ghost liveness model, every case correct"
else
  echo "FAIL: ghost liveness model"
  status=1
fi
exit $status
