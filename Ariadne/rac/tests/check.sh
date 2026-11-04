#!/bin/sh
# Tests of gen_twins.py beyond B1 (B1 itself: ../../bench/b1/rac/check.sh).
#   From this directory:  ./check.sh      (re-runs itself in the M0 image)
#   1. shapes.c (lseg, tree, bst) and guards.c (review regressions):
#      generate, compile with -Wall -Werror, run <name>_test.c under
#      ASan + UBSan; the builtins guards_spec.h calls are declared;
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

# ---- 1. shapes, guards ------------------------------------------------
unit() {  # unit <name>: generate <name>.c, build and run <name>_test.c
  n=$1
  if python3 -I "$RAC/gen_twins.py" "$n.c" "$B/$n" --prefix "$n" \
       --include "$n.h" > "$B/$n.gen.log" 2>&1 &&
     gcc $SAN -I . -I "$B/$n" -I "$RAC" "${n}_test.c" \
       "$B/$n/${n}_twins.c" "$RAC/rac_rt.c" -o "$B/${n}_test" \
       > "$B/$n.build.log" 2>&1; then
    ok=0
    for _ in 1 2 3 4 5 6 7 8 9 10; do  # ASan start-up retries, as in B1
      # GCC 12's ASan sometimes never starts here (endless DEADLYSIGNAL):
      # time-limited, output capped, retried
      ( timeout 60 "./$B/${n}_test" 2>&1; echo $? > "$B/rc" ) |
        head -c 100000 > "$B/$n.run.log"
      [ "$(cat "$B/rc")" = 0 ] && { ok=1; break; }
      head -1 "$B/$n.run.log" | grep -q '^AddressSanitizer:DEADLYSIGNAL' ||
        break
    done
    if [ $ok = 1 ]; then
      echo "PASS: $(cat "$B/$n.run.log")  [$(head -1 "$B/$n.gen.log")]"
    else
      echo "FAIL: $n twin unit tests:"; cat "$B/$n.run.log"; status=1
    fi
  else
    echo "FAIL: $n: generate or build:"
    cat "$B/$n.gen.log" "$B/$n.build.log" | head -40; status=1
  fi
}
unit shapes
unit guards
# every builtin the executable spec block calls is declared in the header
if python3 - "$B/guards/guards_spec.h" "$B/guards/guards_twins.h" <<'EOF'
import re, sys
spec, hdr = open(sys.argv[1]).read(), open(sys.argv[2]).read()
used = set(re.findall(r"\b(rac_\w+)\(", spec))
declared = set(re.findall(r"\b(rac_\w+)\(", hdr)) | {
    "rac_heap", "rac_dead", "rac_heap_of", "rac_dead_of", "rac_length",
    "rac_nth", "rac_tail", "rac_concat"}
missing = sorted(used - declared)
print("missing: " + ", ".join(missing) if missing else
      "ok: " + ", ".join(sorted(u for u in used if u.startswith("rac_cons"))))
sys.exit(1 if missing else 0)
EOF
then
  echo "PASS: guards_spec.h calls only declared builtins"
else
  echo "FAIL: guards_spec.h calls undeclared builtins"; status=1
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
