#!/bin/sh
# sglib's own self-test (../sglib/selftest.c, vendored unmodified) under
# ASan + UBSan, with a fixed seed.
#   From this directory:  ./check.sh [seed]      (default seed 1)
# Re-runs itself inside the M0 image (../../env/run.sh).
#   1. build selftest.c with gcc -fsanitize=address,undefined (no
#      recovery: the first report aborts the run), linked with seed.c
#      under -Wl,--wrap=time, so main's srandom(time(NULL)) gets the
#      seed; the link is checked to call __wrap_time;
#   2. run it: all eight tests, REPEAT (10) passes each; sglib's own
#      assert()s check the results.  Pass = exit status 0, no report.
set -u
if ! command -v e-acsl-gcc >/dev/null 2>&1; then
  exec ../../env/run.sh sh ./check.sh "$@"
fi
seed=${1:-1}
SG=/ariadne/bench/sglib
B=build
rm -rf "$B" && mkdir -p "$B"
SAN="-g -O1 -fsanitize=address,undefined -fno-sanitize-recover=all"

if ! gcc $SAN -I "$SG" "$SG/selftest.c" seed.c -Wl,--wrap=time \
       -o "$B/selftest.asan" > "$B/build.log" 2>&1; then
  cat "$B/build.log"; echo "FAIL: ASan+UBSan build of selftest.c"; exit 1
fi
if ! objdump -d "$B/selftest.asan" | grep -q 'call.*<__wrap_time>'; then
  echo "FAIL: selftest.c's call to time() is not wrapped"; exit 1
fi
# GCC 12's ASan sometimes fails to start under this kernel's address-space
# randomisation (an endless "AddressSanitizer:DEADLYSIGNAL" before main;
# see ../b1/rac/check.sh); such a start is retried, up to 10 times.
for try in 1 2 3 4 5 6 7 8 9 10; do
  ( SELFTEST_SEED=$seed ASAN_OPTIONS=detect_leaks=1 timeout 600 \
      "./$B/selftest.asan" 2>&1; echo "$?" > "$B/run.rc" ) \
    | head -c 200000 > "$B/run.log"
  rc=$(cat "$B/run.rc")
  head -1 "$B/run.log" | grep -q '^AddressSanitizer:DEADLYSIGNAL' || break
done
if [ "$rc" -eq 0 ] && [ ! -s "$B/run.log" ]; then
  echo "PASS: sglib selftest.c under ASan+UBSan, seed $seed (start-up retries: $((try - 1)))"
else
  echo "FAIL: sglib selftest.c under ASan+UBSan, seed $seed (exit $rc):"
  tail -30 "$B/run.log"; exit 1
fi
