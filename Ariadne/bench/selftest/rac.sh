#!/bin/sh
# sglib's self-test against B1's public contracts (plan Q12, step 0 style).
#   From this directory:  ./rac.sh [seed]      (default seed 1)
# Re-runs itself inside the M0 image (../../env/run.sh).  selftest_dl.c
# includes ../sglib/selftest.c unmodified and instantiates the spec
# template (../sglib_spec) at DoubleLinkedList / previous / next; main runs
# double_linked_list_test once.  B1's RAC pipeline (../b1/rac,
# ../../rac) does the rest:
#   0. generate: selftest_dl.c with the template expanded
#      (../../harness/acsl_expand.py); the twins (gen_twins.py, the C types
#      taken from selftest.c, the iterator's witnesses from
#      ../sglib_spec/rac_witnesses.json); selftest_dl_rac.c (gen_rac.py
#      --cov: the clauses named for the coverage report);
#   1. ASan + UBSan build of selftest_dl.c (ACSL ignored): the test itself,
#      then the operation sequences (main's `ops` mode) for each seed of
#      $OPS_SEEDS (default 1 2 3 4 5), $OPS_N operations each (400);
#   2. E-ACSL build with RTE (-rte-initialized @all, as for WP), every
#      contract of the six specified functions checked at each call;
#      ../../rac/rac_collect.c counts every evaluation of every check,
#      records each failed check and lets the run go on;
#      the table of failed checks is printed (`FAILED count kind name in
#      function at file:line: predicate`); then a diagnostic run with
#      every node zero-filled at allocation (argument `zero`), to separate
#      the failures that all_init causes from the others; and two probes,
#      one add of a fresh node to an empty list with only its n written
#      (`probe`) and with every field written (`probefull`); then the
#      operation sequences, as in step 1; then the coverage report of the
#      self-test and the sequences (../../rac/coverage.py, into
#      build/rac/coverage.md).
# Exit status 0 if both builds ran to the end and no check failed in an
# operation sequence; the self-test's failed checks are the result, not an
# error.
set -u
if ! command -v e-acsl-gcc >/dev/null 2>&1; then
  exec ../../env/run.sh sh ./rac.sh "$@"
fi
seed=${1:-1}
OPS_SEEDS=${OPS_SEEDS:-1 2 3 4 5}   # operation-sequence seeds
OPS_N=${OPS_N:-400}                 # operations per sequence
RAC=/ariadne/rac
B1RAC=/ariadne/bench/b1/rac
SG=/ariadne/bench/sglib
INC="-I/ariadne/plugin/share -I/ariadne/bench/sglib_spec -I$SG -I$RAC"
B=build/rac
TW=$B/twins
SAN="-g -O1 -fsanitize=address,undefined -fno-sanitize-recover=all"
rm -rf "$B" && mkdir -p "$B/src" "$TW"
status=0

# ---- 0. generate -----------------------------------------------------
python3 -I /ariadne/harness/acsl_expand.py selftest_dl.c "$B/src/selftest_dl.c" \
  --cpp-args="$INC" --keep ARIADNE_ALLOC,ARIADNE_FREE ||
  { echo "FAIL: acsl_expand.py"; exit 1; }
# The C types for the twins: struct MyIntList and its typedefs, as
# selftest.c writes them.
python3 -I -c '
import re, sys
s = open(sys.argv[1]).read()
m = re.search(r"struct MyIntList \{.*?\n\};\n", s, re.S)
t = re.findall(r"typedef struct MyIntList \w+;\n", s)
open(sys.argv[2], "w").write("#ifndef ST_TYPES_H\n#define ST_TYPES_H\n"
                             + m.group(0) + "".join(t) + "#endif\n")
' "$SG/selftest.c" "$B/src/st_types.h"
cp "$B/src/st_types.h" "$TW/"
# The iterator's witnesses (iter_pre, iter_ok): ../sglib_spec.
python3 -I "$RAC/gen_twins.py" "$B/src/selftest_dl.c" "$TW" \
  --include st_types.h --cpp-args="$INC" \
  --witness-hints /ariadne/bench/sglib_spec/rac_witnesses.json \
  > "$TW.log" 2>&1 ||
  { cat "$TW.log"; echo "FAIL: gen_twins.py"; exit 1; }
BUILTINS=$(python3 -c 'import json, sys
print(",".join(json.load(open(sys.argv[1]))["builtins"]))' "$TW/rac_twins.json")
mkdir -p "$B/e"
python3 -I "$B1RAC/gen_rac.py" "$B/src/selftest_dl.c" "$B/e" "$TW" \
  --name selftest_dl --no-harness --cov > "$B/e/gen.log" ||
  { cat "$B/e/gen.log"; echo "FAIL: gen_rac.py"; exit 1; }
echo "step 0: $(head -1 "$TW.log"); $(cat "$B/e/gen.log")"
grep -E "selftest_dl.c:[0-9]+: (requires|ensures)" "$B/e/annotations.txt" \
  | sed 's/^/    /'

# ---- 1. sanitizers ---------------------------------------------------
# GCC 12's ASan sometimes fails to start under this kernel's address-space
# randomisation (see ../b1/rac/check.sh); such a start is retried.
run_log() {  # run_log <log> <cmd...>
  log=$1; shift
  for _ in 1 2 3 4 5 6 7 8 9 10; do
    ( timeout 1200 "$@" 2>&1; echo "$?" > "$log.rc" ) | head -c 2000000 > "$log"
    head -1 "$log" | grep -q '^AddressSanitizer:DEADLYSIGNAL' || break
  done
  return "$(cat "$log.rc")"
}
if gcc $SAN $INC selftest_dl.c "$RAC/rac_rt.c" -o "$B/selftest_dl.asan" \
     > "$B/asan.build.log" 2>&1 &&
   ASAN_OPTIONS=detect_leaks=1 run_log "$B/asan.log" "./$B/selftest_dl.asan" "$seed" &&
   [ ! -s "$B/asan.log" ]; then
  echo "PASS: ASan+UBSan build of selftest_dl.c, seed $seed"
else
  echo "FAIL: ASan+UBSan build of selftest_dl.c:"
  tail -20 "$B/asan.build.log" "$B/asan.log"; status=1
fi
# operation sequences (main's `ops` mode), several seeds
for s in $OPS_SEEDS; do
  if ASAN_OPTIONS=detect_leaks=1 run_log "$B/asan.ops$s.log" \
       "./$B/selftest_dl.asan" "$s" ops "$OPS_N" &&
     [ "$(cat "$B/asan.ops$s.log")" = "$(grep '^ops: done' "$B/asan.ops$s.log")" ]; then
    :
  else
    echo "FAIL: ASan+UBSan operation sequence, seed $s:"
    tail -20 "$B/asan.ops$s.log"; status=1
  fi
done
[ $status -eq 0 ] && echo "PASS: ASan+UBSan operation sequences, seeds $OPS_SEEDS ($OPS_N operations each)"

# ---- 2. E-ACSL -------------------------------------------------------
d=$B/e
if ( cd "$d" &&
     cp "$B1RAC/rac.h" ../twins/rac_twins.h "$RAC/rac_rt.h" . &&
     frama-c -e-acsl-builtins="$BUILTINS" -machdep gcc_x86_64 \
       -no-frama-c-stdlib -keep-unused-functions all \
       -cpp-extra-args="-D_DEFAULT_SOURCE -D__NO_CTYPE -D__FC_MACHDEP_X86_64 -DRAC_KEEP_FREED $INC" \
       -no-warn-unaligned-pointer \
       selftest_dl_rac.c -rte -rte-initialized @all -rte-select=@all,-main \
       -then -print -ocode selftest_dl_rac.rte.c &&
     gcc -O1 -g -c -I. -I../src ../twins/rac_twins.c -o rac_twins.o &&
     gcc -O1 -g -c -I. "$RAC/rac_rt.c" -o rac_rt.o &&
     e-acsl-gcc -c -F "-e-acsl-builtins=$BUILTINS -e-acsl-no-assert-print-data" \
       --external-assert "$RAC/rac_collect.c" \
       -l "$PWD/rac_twins.o $PWD/rac_rt.o" \
       -e "-include $PWD/rac_twins.h" -o selftest_dl_rac.frama.c \
       -O selftest_dl_rac selftest_dl_rac.rte.c ) > "$d/eacsl.build.log" 2>&1
then
  rm -f "$B/cov."*.tsv
  run_log "$d/eacsl.log" "./$d/selftest_dl_rac.e-acsl" "$seed"
  rc=$?
  grep '^COV' "$d/eacsl.log" | cut -f2- > "$B/cov.selftest.tsv"
  if [ "$rc" -eq 0 ]; then
    echo "PASS: E-ACSL run of selftest_dl.c to the end, seed $seed"
  else
    echo "FAIL: E-ACSL run of selftest_dl.c stopped (exit $rc):"
    grep -v '^FAILED' "$d/eacsl.log" | tail -20; status=1
  fi
  grep -E '^(FAILED|checks failed)' "$d/eacsl.log"
  # Diagnostic run: every node fully written by st_malloc, so all_init
  # holds and the failures that remain have other causes.
  echo "diagnostic run (nodes zero-filled at allocation):"
  run_log "$d/eacsl.zero.log" "./$d/selftest_dl_rac.e-acsl" "$seed" zero ||
    { echo "FAIL: diagnostic E-ACSL run stopped"; status=1; }
  grep -E '^(FAILED|checks failed)' "$d/eacsl.zero.log"
  # Probes: one add of a fresh node to an empty list, with only n
  # written (as the self-test does) and with every field written.
  for m in probe probefull; do
    echo "probe run ($m):"
    run_log "$d/eacsl.$m.log" "./$d/selftest_dl_rac.e-acsl" "$seed" "$m" ||
      { echo "FAIL: probe run $m stopped"; status=1; }
    grep -E '^(FAILED|checks failed)' "$d/eacsl.$m.log"
  done
  # operation sequences under E-ACSL, every contract checked at each call
  t=$(date +%s)
  fails=0
  for s in $OPS_SEEDS; do
    run_log "$d/eacsl.ops$s.log" \
      "./$d/selftest_dl_rac.e-acsl" "$s" ops "$OPS_N" ||
      { echo "FAIL: E-ACSL operation sequence, seed $s stopped"; status=1; }
    grep '^COV' "$d/eacsl.ops$s.log" | cut -f2- >> "$B/cov.ops.tsv"
    n=$(grep -c '^FAILED' "$d/eacsl.ops$s.log")
    fails=$((fails + n))
    grep '^FAILED' "$d/eacsl.ops$s.log" | sed "s/^/    seed $s: /"
  done
  echo "E-ACSL operation sequences, seeds $OPS_SEEDS ($OPS_N operations each): $fails failing check(s), $(( $(date +%s) - t )) s"
  [ "$fails" -eq 0 ] || status=1
  python3 -I "$RAC/coverage.py" "$d/coverage_map.json" "$d/annotations.txt" \
    "$B/coverage.md" selftest="$B/cov.selftest.tsv" ops="$B/cov.ops.tsv"
else
  echo "FAIL: E-ACSL build of selftest_dl.c:"; tail -30 "$d/eacsl.build.log"
  status=1
fi
exit $status
