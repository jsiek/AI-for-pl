#!/bin/sh
# Change #2, verification refactor (../CHANGES.md): behaviour unchanged.
#   1. the refactored sglib.h (it_next_calls.py) differs from the vendored
#      one in exactly the two loop lines;
#   2. sglib's self-test (../../sglib/selftest.c, unmodified), built under
#      ASan + UBSan against the vendored and against the refactored
#      sglib.h, gives the same output and exit status for seeds 1, 7 and
#      12345 (and passes).  Its doubly linked list test iterates with
#      sglib_DoubleLinkedList_it_init_on_equal and myListCmp, so both
#      refactored loops run.
# Re-runs itself in the M0 image.
set -u
if ! command -v e-acsl-gcc >/dev/null 2>&1; then
  exec ../../../env/run.sh sh ./check.sh "$@"
fi
SG=/ariadne/bench/sglib
B=build
rm -rf "$B" && mkdir -p "$B/orig" "$B/refactored"
status=0
cp "$SG/selftest.c" "$SG/sglib.h" "$B/orig/"
cp "$SG/selftest.c" "$B/refactored/"
python3 -I it_next_calls.py "$SG/sglib.h" "$B/refactored/sglib.h" || exit 1
n=$(diff "$B/orig/sglib.h" "$B/refactored/sglib.h" | grep -c '^[<>]')
if [ "$n" -eq 4 ]; then
  echo "PASS: the refactored sglib.h differs in exactly two lines"
else
  echo "FAIL: sglib.h diff has $n changed lines, expected 4"; status=1
fi
SAN="-g -O1 -fsanitize=address,undefined -fno-sanitize-recover=all"
for v in orig refactored; do
  gcc $SAN "$B/$v/selftest.c" /ariadne/bench/selftest/seed.c -Wl,--wrap=time \
    -o "$B/$v/selftest" > "$B/$v/build.log" 2>&1 ||
    { cat "$B/$v/build.log"; exit 1; }
done
for seed in 1 7 12345; do
  for v in orig refactored; do
    for _ in 1 2 3 4 5 6 7 8 9 10; do   # ASan start-up retries (../rac/check.sh)
      ( SELFTEST_SEED=$seed timeout 600 "./$B/$v/selftest" 2>&1
        echo "exit=$?" ) | head -c 200000 > "$B/$v/out.$seed"
      head -1 "$B/$v/out.$seed" | grep -q DEADLYSIGNAL || break
    done
  done
  if cmp -s "$B/orig/out.$seed" "$B/refactored/out.$seed" &&
     [ "$(cat "$B/orig/out.$seed")" = "exit=0" ]; then
    echo "PASS: seed $seed: same output (passes, no sanitizer report)"
  else
    echo "FAIL: seed $seed:"; tail -5 "$B/orig/out.$seed" \
      "$B/refactored/out.$seed"; status=1
  fi
done
exit $status
