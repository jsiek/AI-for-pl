#!/bin/sh
# B1a runtime checking (plan section 5 step 0; plan Q10, Q11's step-0
# rule).  From this directory:  ./check.sh [runs [seed [large [quick]]]]
#   (defaults 300 1 200; the 4th argument is accepted for the harness's
#   command line and changes nothing: the mutants' anchors are C code, so
#   they fit any annotated B1a source, and always run)
# $SRC is the annotated source checked (default ../b1a_ref.c, B1's
# certified annotations on B1a's driver; the harness points it at the
# annotator's copy of b1a_frozen.c).
# B1's tools are reused (../../b1/rac: gen_rac.py, rac_alloc.c, rac.h,
# classify.py, rac_twins_test.c, and rac_main.c with B1a's oracle,
# -DRAC_ORACLE_B1A).  Re-runs itself inside the M0 image, where /ariadne
# is the Ariadne/ directory.  Steps, each timed:
#   0. generate: $SRC with the macros inside its annotations expanded,
#      the twins (../../../rac/gen_twins.py), b1_rac.c for $SRC, for the
#      coverage build, and for B1a's runtime mutants
#      (../../../q10/mutants.py: vacuity, uaf, nullchk, noinit);
#   1. sanitizers: ASan + UBSan, real malloc/free, the random driver;
#   2. twins: unit tests on good and corrupt heaps;
#   3. E-ACSL: RTE (-rte-initialized @all), E-ACSL with the twins; run;
#   3b. coverage: per-clause report build/coverage.md
#      (../../../rac/coverage.py); fails if a check fails;
#   4. mutants: steps 1 and 3 on each; each must be caught (a sanitizer
#      error, a failed E-ACSL check, or the oracle).  nowashead and
#      noassign only weaken add's contract and run correctly, so they
#      are WP's to reject, not step 0's.
# $SRC must pass steps 1-3b and every mutant must be caught.
set -u
if ! command -v e-acsl-gcc >/dev/null 2>&1; then
  exec ../../../env/run.sh sh ./check.sh "$@"
fi
runs=${1:-300} seed=${2:-1} large=${3:-200}
B1A=/ariadne/bench/b1a
SRC=$B1A/b1a_ref.c
R1=/ariadne/bench/b1/rac
B=build
CPP_ARGS="-I/ariadne/plugin/share -I/ariadne/bench/b1a/spec_full"
ORACLE=-DRAC_ORACLE_B1A
status=0
rm -rf "$B" && mkdir -p "$B"

now() { date +%s.%N; }
lap() { python3 -c "import sys; print('%.1f' % (float(sys.argv[2]) - float(sys.argv[1])))" "$1" "$(now)"; }

MUTANTS="vacuity uaf nullchk noinit"
RAC=/ariadne/rac
TW=$B/twins
SAN="-std=c99 -g -O1 -fsanitize=address,undefined -fno-sanitize-recover=all"

# ---- 0. generate -----------------------------------------------------
t=$(now)
mkdir -p "$B/src"
python3 -I /ariadne/harness/acsl_expand.py "$SRC" "$B/src/orig.c" \
  --cpp-args="$CPP_ARGS" --keep ARIADNE_ALLOC,ARIADNE_FREE ||
  { echo "FAIL: acsl_expand.py on $SRC"; exit 1; }
python3 -I "$RAC/gen_twins.py" "$B/src/orig.c" "$TW" --include b1_types.h \
  --witness-hints /ariadne/bench/b1a/spec_full/rac_witnesses.json \
  --cpp-args="$CPP_ARGS" > "$TW.log" 2>&1 ||
  { cat "$TW.log"; echo "FAIL: gen_twins.py"; exit 1; }
BUILTINS=$(python3 -c 'import json, sys
print(",".join(json.load(open(sys.argv[1]))["builtins"]))' "$TW/rac_twins.json")
python3 -I /ariadne/q10/mutants.py "$B/src/orig.c" "$B/src" $MUTANTS ||
  { echo "FAIL: q10/mutants.py on $SRC"; exit 1; }
for v in orig $MUTANTS; do
  mkdir -p "$B/$v"
  python3 -I "$R1/gen_rac.py" "$B/src/$v.c" "$B/$v" "$TW" > "$B/$v/gen.log" ||
    { cat "$B/$v/gen.log"; echo "FAIL: gen_rac.py on $v"; exit 1; }
done
mkdir -p "$B/cov"
cp "$B/src/orig.c" "$B/src/cov.c"
python3 -I "$R1/gen_rac.py" "$B/src/cov.c" "$B/cov" "$TW" --cov \
  > "$B/cov/gen.log" ||
  { cat "$B/cov/gen.log"; echo "FAIL: gen_rac.py --cov"; exit 1; }
echo "step 0 (generate twins, b1_rac.c x6): $(lap "$t") s; $(head -1 "$TW.log")"
echo "    $(cat "$B/orig/gen.log")"

# ---- 1. sanitizers ---------------------------------------------------
san_build() {  # san_build <variant>
  gcc $SAN $ORACLE -I "$B/$1" -I "$TW" -I "$RAC" -I /ariadne/plugin/share \
    -I /ariadne/bench/b1a/spec_full -I "$R1" \
    "$B/src/$1.c" "$R1/rac_alloc.c" "$TW/rac_twins.c" "$RAC/rac_rt.c" \
    "$R1/rac_main.c" -o "$B/$1/b1.asan" > "$B/$1/asan.build.log" 2>&1
}
run_log() {  # run_log <log> <cmd...>: as ../../b1/rac/check.sh
  log=$1; shift
  ( timeout 120 "$@" 2>&1; echo "$?" > "$log.rc" ) | head -c 200000 > "$log"
  rc=$(cat "$log.rc")
  echo "exit=$rc" >> "$log"
  return "$rc"
}
san_exec() {  # retries ASan's DEADLYSIGNAL start-up failures, as B1's
  for _ in 1 2 3 4 5 6 7 8 9 10; do
    run_log "$@" && return 0
    rc=$?
    head -1 "$1" | grep -q '^AddressSanitizer:DEADLYSIGNAL' || return $rc
    echo "$1" >> "$B/asan_retries"
  done
  return $rc
}
san_run() {
  ASAN_OPTIONS=detect_leaks=1 san_exec "$B/$1/asan.log" \
    "./$B/$1/b1.asan" "$runs" "$seed" "$large"
}
t=$(now)
if san_build orig && san_run orig; then
  echo "PASS: ASan+UBSan build of the source: $(grep "^ok:" "$B/orig/asan.log")"
else
  echo "FAIL: ASan+UBSan build of the source:"; tail -20 "$B/orig/asan.log" \
    "$B/orig/asan.build.log"; status=1
fi
echo "step 1 (sanitizers): $(lap "$t") s"

# ---- 2. twin unit tests ----------------------------------------------
t=$(now)
if gcc $SAN -I "$B/orig" -I "$TW" -I "$RAC" -I "$R1" "$R1/rac_twins_test.c" \
     "$R1/rac_alloc.c" "$TW/rac_twins.c" "$RAC/rac_rt.c" \
     -o "$B/twins_test" > "$B/twins_test.log" 2>&1 &&
   san_exec "$B/twins_test.run.log" "./$B/twins_test"; then
  cat "$B/twins_test.run.log" >> "$B/twins_test.log"
  echo "PASS: $(grep 'twin unit tests' "$B/twins_test.log")"
else
  echo "FAIL: twin unit tests:"; cat "$B/twins_test.log" \
    "$B/twins_test.run.log"; status=1
fi
echo "step 2 (twin unit tests): $(lap "$t") s"

# ---- 3. E-ACSL -------------------------------------------------------
eacsl_build() {  # eacsl_build <variant> [extra e-acsl-gcc options]
  d=$B/$1
  extra=${2:-}
  ( cd "$d" &&
    cp "$R1/rac.h" ../twins/rac_twins.h "$RAC/rac_rt.h" "$R1/rac_alloc.c" \
       "$R1/rac_main.c" . &&
    frama-c -e-acsl-builtins="$BUILTINS" -machdep gcc_x86_64 \
      -no-frama-c-stdlib -keep-unused-functions all \
      -cpp-extra-args="-std=c99 -D_DEFAULT_SOURCE -D__NO_CTYPE -D__FC_MACHDEP_X86_64 -DRAC_KEEP_FREED $ORACLE -I/ariadne/bench/b1a/spec_full" \
      -no-warn-unaligned-pointer \
      b1_rac.c -rte -rte-initialized @all -rte-select=@all,-main,-rng \
      -then -print -ocode b1_rac.rte.c &&
    gcc -std=c99 -O1 -g -c -I. ../twins/rac_twins.c -o rac_twins.o &&
    gcc -std=c99 -O1 -g -c -I. "$RAC/rac_rt.c" -o rac_rt.o &&
    e-acsl-gcc -c -F "-e-acsl-builtins=$BUILTINS -e-acsl-no-assert-print-data" \
      $extra -l "$PWD/rac_twins.o $PWD/rac_rt.o" \
      -e "-include $PWD/rac_twins.h" -o b1_rac.frama.c -O b1_rac \
      b1_rac.rte.c ) > "$d/eacsl.build.log" 2>&1
}
eacsl_run() {
  run_log "$B/$1/eacsl.log" "./$B/$1/b1_rac.e-acsl" "$runs" "$seed" "$large"
}
t=$(now)
if eacsl_build orig; then
  tb=$(lap "$t")
  t=$(now)
  if eacsl_run orig; then
    echo "PASS: E-ACSL build of the source: $(grep "^ok:" "$B/orig/eacsl.log")"
  else
    echo "FAIL: E-ACSL run of the source:"; tail -20 "$B/orig/eacsl.log"
    status=1
  fi
  echo "step 3 (E-ACSL): build $tb s, run $(lap "$t") s"
else
  echo "FAIL: E-ACSL build of the source:"; tail -30 "$B/orig/eacsl.build.log"
  exit 1
fi
python3 -I "$R1/classify.py" warnings "$B/orig/eacsl.build.log" \
  > "$B/eacsl_warnings.txt"
echo "E-ACSL ignored $(grep -c 'Ignoring annotation' "$B/eacsl_warnings.txt") annotation(s) (all warnings: build/eacsl_warnings.txt)"

# ---- 3b. coverage (plan Q11 step 0) ----------------------------------
t=$(now)
if eacsl_build cov "--external-assert $RAC/rac_collect.c"; then
  eacsl_run cov
  grep '^COV' "$B/cov/eacsl.log" | cut -f2- > "$B/cov.driver.tsv"
  grep -E '^(FAILED|checks failed)' "$B/cov/eacsl.log" | sed 's/^/    /'
  grep -q '^checks failed: 0 distinct' "$B/cov/eacsl.log" || status=1
  python3 -I "$RAC/coverage.py" "$B/cov/coverage_map.json" \
    "$B/cov/annotations.txt" "$B/coverage.md" driver="$B/cov.driver.tsv"
else
  echo "FAIL: E-ACSL coverage build:"; tail -30 "$B/cov/eacsl.build.log"
  status=1
fi
echo "step 3b (coverage): $(lap "$t") s"

# ---- 4. mutants ------------------------------------------------------
t=$(now)
for m in $MUTANTS; do
  ( if san_build "$m"; then san_run "$m"; else echo "build failed" > "$B/$m/asan.log"; fi
    if eacsl_build "$m"; then eacsl_run "$m"; else echo "build failed" > "$B/$m/eacsl.log"; fi
  ) &
done
wait
printf '%-10s %-22s %s\n' mutant "ASan+UBSan" "E-ACSL (first check to fire)"
for m in $MUTANTS; do
  gs=$(python3 -I "$R1/classify.py" san "$B/$m/asan.log")
  ge=$(python3 -I "$R1/classify.py" eacsl "$B/$m/eacsl.log")
  case "$gs/$ge" in
    -/-|crash*/-|-/crash*|crash*/crash*)
      verdict=MISSED; status=1 ;;
    *) verdict=ok ;;
  esac
  printf '%-10s %-22s %s  [%s]\n' "$m" "$gs" "$ge" "$verdict" | sed "s/ubsan: member access within null pointer of type 'struct dllist'/ubsan: null member access/"
done
echo "step 4 (mutants x4, both builds): $(lap "$t") s"
echo "not for step 0: nowashead, noassign (contract weakenings; WP's to reject)"
echo "ASan start-up retries (DEADLYSIGNAL): $(cat "$B/asan_retries" 2>/dev/null | wc -l)"
[ "$status" -eq 0 ] && echo "PASS: runtime checking of B1a" || echo "FAIL: runtime checking of B1a"
exit $status
