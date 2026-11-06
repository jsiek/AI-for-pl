#!/bin/sh
# Bug fix #1 (../BUGFIXES.md): the test.  sglib's samples/dllist.c, built
# with UBSan, on extreme values:
#   dllist -5 2147483647 -2147483648 3
#   1. upstream (../../sglib/dllist.c, unmodified): UBSan reports the
#      signed overflow in DLLIST_COMPARATOR and the list is printed
#      unsorted -- the test FAILS on the original code, as it must;
#   2. fixed (the same file with B1's comparator, written into build/ at
#      run time): no report, and the list is printed sorted.
# Pass = both outcomes as stated.  Re-runs itself in the M0 image.
set -u
if ! command -v e-acsl-gcc >/dev/null 2>&1; then
  exec ../../../env/run.sh sh ./cmp_overflow.sh "$@"
fi
SG=/ariadne/bench/sglib
B=build
rm -rf "$B" && mkdir -p "$B"
OLD='#define DLLIST_COMPARATOR(e1, e2) (e1->i - e2->i)'
NEW='#define DLLIST_COMPARATOR(e1, e2) ((e1->i > e2->i) - (e1->i < e2->i))'
[ "$(grep -cxF "$OLD" "$SG/dllist.c")" -eq 1 ] ||
  { echo "FAIL: upstream comparator line not found"; exit 1; }
cp "$SG/dllist.c" "$B/upstream.c"
python3 -c 'import sys
s = open(sys.argv[1]).read()
open(sys.argv[2], "w").write(s.replace(sys.argv[3], sys.argv[4]))' \
  "$SG/dllist.c" "$B/fixed.c" "$OLD" "$NEW"
status=0
ARGS="-5 2147483647 -2147483648 3"
SORTED="-2147483648 -5 3 2147483647 "
for v in upstream fixed; do
  gcc -g -O0 -fsanitize=undefined -I "$SG" "$B/$v.c" -o "$B/$v" \
    > "$B/$v.build.log" 2>&1 || { cat "$B/$v.build.log"; exit 1; }
  # shellcheck disable=SC2086
  "./$B/$v" $ARGS > "$B/$v.out" 2> "$B/$v.err"
  echo "$v: $(head -1 "$B/$v.out")| $(grep -c 'runtime error' "$B/$v.err") UBSan report(s)"
  grep 'runtime error' "$B/$v.err" | head -2 | sed 's/^/    /'
done
if grep -q 'signed integer overflow' "$B/upstream.err" &&
   [ "$(head -1 "$B/upstream.out")" != "$SORTED" ]; then
  echo "PASS: upstream fails (UBSan signed overflow, list unsorted)"
else
  echo "FAIL: upstream did not fail as expected"; status=1
fi
if [ ! -s "$B/fixed.err" ] && [ "$(head -1 "$B/fixed.out")" = "$SORTED" ]; then
  echo "PASS: fixed sorts the list, no UBSan report"
else
  echo "FAIL: fixed version"; status=1
fi
exit $status
