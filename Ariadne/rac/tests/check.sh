#!/bin/sh
# Tests of gen_twins.py beyond B1 (B1 itself: ../../bench/b1/rac/check.sh).
#   From this directory:  ./check.sh      (re-runs itself in the M0 image)
#   1. shapes.c (lseg, tree, bst): generate, compile with -Wall -Werror,
#      run shapes_test.c under ASan + UBSan;
#   2. untranslatable.c: the generator must refuse each definition by
#      name, with the reasons in untranslatable.expected, and exit 1.
set -u
if ! command -v frama-c >/dev/null 2>&1; then
  exec ../../env/run.sh sh ./check.sh "$@"
fi
B=build
RAC=/ariadne/rac
status=0
rm -rf "$B" && mkdir -p "$B"
SAN="-std=c99 -g -O1 -Wall -Wextra -Werror -fsanitize=address,undefined -fno-sanitize-recover=all"

# ---- 1. shapes ---------------------------------------------------------
if python3 -I "$RAC/gen_twins.py" shapes.c "$B/shapes" --prefix shapes \
     --include shapes.h > "$B/shapes.gen.log" 2>&1 &&
   gcc $SAN -I . -I "$B/shapes" -I "$RAC" shapes_test.c \
     "$B/shapes/shapes_twins.c" "$RAC/rac_rt.c" -o "$B/shapes_test" \
     > "$B/shapes.build.log" 2>&1; then
  ok=0
  for _ in 1 2 3 4 5 6 7 8 9 10; do  # ASan start-up retries, as in B1
    # GCC 12's ASan sometimes never starts here (endless DEADLYSIGNAL):
    # time-limited, output capped, retried
    ( timeout 60 "./$B/shapes_test" 2>&1; echo $? > "$B/rc" ) |
      head -c 100000 > "$B/shapes.run.log"
    [ "$(cat "$B/rc")" = 0 ] && { ok=1; break; }
    head -1 "$B/shapes.run.log" | grep -q '^AddressSanitizer:DEADLYSIGNAL' ||
      break
  done
  if [ $ok = 1 ]; then
    echo "PASS: $(cat "$B/shapes.run.log")  [$(head -1 "$B/shapes.gen.log")]"
  else
    echo "FAIL: shapes twin unit tests:"; cat "$B/shapes.run.log"; status=1
  fi
else
  echo "FAIL: shapes: generate or build:"
  cat "$B/shapes.gen.log" "$B/shapes.build.log" | head -40; status=1
fi

# ---- 2. untranslatable -------------------------------------------------
python3 -I "$RAC/gen_twins.py" untranslatable.c "$B/untr" --prefix untr \
  --include shapes.h > "$B/untr.gen.log" 2>&1
rc=$?
grep 'NOT TRANSLATED' "$B/untr/untr_twins.txt" > "$B/untr.got"
if [ $rc = 1 ] && diff untranslatable.expected "$B/untr.got" > "$B/untr.diff"
then
  echo "PASS: untranslatable.c: $(wc -l < "$B/untr.got") definitions refused, as expected"
else
  echo "FAIL: untranslatable.c (exit $rc):"; cat "$B/untr.diff"; status=1
fi
[ "$status" -eq 0 ] && echo "PASS: gen_twins tests" || echo "FAIL: gen_twins tests"
exit $status
