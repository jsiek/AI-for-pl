#!/bin/sh
# B1 runtime checking (plan section 5 step 0, "test first").
#   From this directory:  ./check.sh [runs [seed [large [quick]]]]
#   (defaults 300 1 200; any 4th argument skips the mutants and the
#   gen_rac.py test, so only $SRC is checked)
# $SRC is the annotated source checked (default b1.c; the harness points
# it at the annotator's copy of b1_frozen.c, which the mutants' anchors
# do not fit).
# Re-runs itself inside the M0 image (../../../env/run.sh), where
# /ariadne is the Ariadne/ directory.  Steps, each timed:
#   0. generate: the twins and the executable spec block from b1.c
#      (../../../rac/gen_twins.py, into build/twins), then b1_rac.c
#      (gen_rac.py) for b1.c and for the seven mutants (../mutants.py,
#      shared with ../check.sh); test_gen_rac.py checks how gen_rac.py
#      splits clauses (operator precedence);
#   1. sanitizers: b1.c with ASan + UBSan (gcc), real malloc/free, driver
#      rac_main.c; MSan is tried (clang) and skipped if unavailable;
#   2. twins: unit tests on good and corrupt heaps, under ASan + UBSan;
#   3. E-ACSL: RTE (-rte-initialized @all, as for WP), then E-ACSL with the
#      twins as builtins, linked with the twins compiled apart; run;
#   4. mutants: steps 1 and 3 on each mutant; a table of what fired.
# b1.c must pass every step; each mutant must give the outcome recorded
# in `expect` below (so a change in what is caught shows up as FAIL).
set -u
if ! command -v e-acsl-gcc >/dev/null 2>&1; then
  exec ../../../env/run.sh sh ./check.sh "$@"
fi
runs=${1:-300} seed=${2:-1} large=${3:-200} quick=${4:-}
B1=/ariadne/bench/b1
SRC=$B1/b1.c
B=build
status=0
rm -rf "$B" && mkdir -p "$B"

now() { date +%s.%N; }
lap() { python3 -c "import sys; print('%.1f' % (float(sys.argv[2]) - float(sys.argv[1])))" "$1" "$(now)"; }

MUTANTS="vacuity uaf uaf_back nullchk nullfirst nulllast noinit"
RAC=/ariadne/rac
TW=$B/twins
SAN="-std=c99 -g -O1 -fsanitize=address,undefined -fno-sanitize-recover=all"

# ---- 0. generate -----------------------------------------------------
t=$(now)
python3 -I "$RAC/gen_twins.py" "$SRC" "$TW" --include b1_types.h \
  --cpp-args="-I/ariadne/plugin/share" > "$TW.log" 2>&1 ||
  { cat "$TW.log"; echo "FAIL: gen_twins.py on b1.c"; exit 1; }
BUILTINS=$(python3 -c 'import json, sys
print(",".join(json.load(open(sys.argv[1]))["builtins"]))' "$TW/rac_twins.json")
mkdir -p "$B/src"
[ -n "$quick" ] && MUTANTS="" ||
  python3 -I "$B1/mutants.py" "$B1/b1.c" "$B/src" > /dev/null
cp "$SRC" "$B/src/orig.c"
for v in orig $MUTANTS; do
  mkdir -p "$B/$v"
  python3 -I gen_rac.py "$B/src/$v.c" "$B/$v" "$TW" > "$B/$v/gen.log" ||
    { cat "$B/$v/gen.log"; echo "FAIL: gen_rac.py on $v"; exit 1; }
done
echo "step 0 (generate twins, b1_rac.c x8): $(lap "$t") s; $(cat "$TW.log" | head -1)"
echo "    $(cat "$B/orig/gen.log")"
if [ -n "$quick" ]; then
  echo "SKIP: gen_rac.py clause splitting (quick)"
elif r=$(python3 -I test_gen_rac.py "$B1/b1.c" "$B/gen_test" "$TW" 2>&1); then
  echo "PASS: gen_rac.py clause splitting: $r"
else
  echo "$r"; echo "FAIL: gen_rac.py clause splitting"; status=1
fi

# ---- 1. sanitizers ---------------------------------------------------
san_build() {  # san_build <variant>
  gcc $SAN -I "$B/$1" -I "$TW" -I "$RAC" -I /ariadne/plugin/share \
    "$B/src/$1.c" rac_alloc.c "$TW/rac_twins.c" "$RAC/rac_rt.c" rac_main.c \
    -o "$B/$1/b1.asan" > "$B/$1/asan.build.log" 2>&1
}
# run_log <log> <cmd...>: run with a time limit; the log (truncated) ends
# with "exit=<code>", and the result is that code.
run_log() {
  log=$1; shift
  ( timeout 120 "$@" 2>&1; echo "$?" > "$log.rc" ) | head -c 200000 > "$log"
  rc=$(cat "$log.rc")
  echo "exit=$rc" >> "$log"
  return "$rc"
}
# GCC 12's ASan sometimes fails to start under this kernel's address-space
# randomisation (an endless "AddressSanitizer:DEADLYSIGNAL" before main;
# about 1 run in 3 here; the container may not disable ASLR); such a start
# is retried, up to 10 times.
san_exec() {  # san_exec <log> <cmd...>
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
  echo "PASS: ASan+UBSan build of b1.c: $(grep "^ok:" "$B/orig/asan.log")"
else
  echo "FAIL: ASan+UBSan build of b1.c:"; tail -20 "$B/orig/asan.log" \
    "$B/orig/asan.build.log"; status=1
fi
echo "int main(void) { return 0; }" > "$B/msan.c"
if clang -fsanitize=memory "$B/msan.c" -o "$B/msan" > "$B/msan.log" 2>&1
then
  echo "MSan available: not wired in yet"   # not the case in ariadne-m0
else
  echo "SKIP: MSan (clang 14 in the image has no MSan runtime)"
fi
echo "step 1 (sanitizers, b1.c): $(lap "$t") s"

# ---- 2. twin unit tests ----------------------------------------------
t=$(now)
if gcc $SAN -I "$B/orig" -I "$TW" -I "$RAC" rac_twins_test.c rac_alloc.c \
     "$TW/rac_twins.c" "$RAC/rac_rt.c" \
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
eacsl_build() {  # eacsl_build <variant>
  d=$B/$1
  ( cd "$d" &&
    cp ../../rac.h ../twins/rac_twins.h "$RAC/rac_rt.h" ../../rac_alloc.c \
       ../../rac_main.c . &&
    frama-c -e-acsl-builtins="$BUILTINS" -machdep gcc_x86_64 \
      -no-frama-c-stdlib -keep-unused-functions all \
      -cpp-extra-args="-std=c99 -D_DEFAULT_SOURCE -D__NO_CTYPE -D__FC_MACHDEP_X86_64" \
      -no-warn-unaligned-pointer \
      b1_rac.c -rte -rte-initialized @all -rte-select=@all,-main,-rng \
      -then -print -ocode b1_rac.rte.c &&
    gcc -std=c99 -O1 -g -c -I. ../twins/rac_twins.c -o rac_twins.o &&
    gcc -std=c99 -O1 -g -c -I. "$RAC/rac_rt.c" -o rac_rt.o &&
    e-acsl-gcc -c -F "-e-acsl-builtins=$BUILTINS -e-acsl-no-assert-print-data" \
      -l "$PWD/rac_twins.o $PWD/rac_rt.o" \
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
    echo "PASS: E-ACSL build of b1.c: $(grep "^ok:" "$B/orig/eacsl.log")"
  else
    echo "FAIL: E-ACSL run of b1.c:"; tail -20 "$B/orig/eacsl.log"; status=1
  fi
  echo "step 3 (E-ACSL, b1.c): build $tb s, run $(lap "$t") s"
else
  echo "FAIL: E-ACSL build of b1.c:"; tail -30 "$B/orig/eacsl.build.log"
  exit 1
fi
python3 -I classify.py warnings "$B/orig/eacsl.build.log" > "$B/eacsl_warnings.txt"
echo "E-ACSL ignored $(grep -c 'Ignoring annotation' "$B/eacsl_warnings.txt") annotation(s) of b1_rac.rte.c (all warnings: build/eacsl_warnings.txt):"
grep 'Ignoring annotation' "$B/eacsl_warnings.txt" | sed 's/^/    /'

# ---- 4. mutants ------------------------------------------------------
# expect <mutant>: the sanitizer outcome and the E-ACSL outcome, as
# printed by classify.py (`-` = runs clean).
expect() {
  case "$1" in
    vacuity)   san='-'; eac='Assertion vacuity in b1' ;;
    uaf)       san='heap-use-after-free'; eac='Precondition in sglib_dllist_get_first' ;;
    uaf_back)  san='heap-use-after-free'; eac='Precondition in sglib_dllist_get_last' ;;
    nullchk)   san="ubsan: member access within null pointer of type 'struct dllist'"
               eac='Assertion rte/mem_access in b1' ;;
    nullfirst) san='-'; eac='Postcondition heads_list in sglib_dllist_get_first' ;;
    nulllast)  san='oracle'; eac='Postcondition last_of_list in sglib_dllist_get_last' ;;
    noinit)    san='oracle'; eac='Precondition elem_init in sglib_dllist_add' ;;
  esac
}
[ -n "$quick" ] && exit $status   # 4th argument: b1.c only
t=$(now)
for m in $MUTANTS; do   # the seven mutants in parallel
  ( if san_build "$m"; then san_run "$m"; else echo "build failed" > "$B/$m/asan.log"; fi
    if eacsl_build "$m"; then eacsl_run "$m"; else echo "build failed" > "$B/$m/eacsl.log"; fi
  ) &
done
wait
printf '%-10s %-22s %s\n' mutant "ASan+UBSan" "E-ACSL (first check to fire)"
for m in $MUTANTS; do
  expect "$m"
  gs=$(python3 -I classify.py san "$B/$m/asan.log")
  ge=$(python3 -I classify.py eacsl "$B/$m/eacsl.log")
  verdict=ok
  [ "$gs" = "$san" ] && [ "$ge" = "$eac" ] || { verdict="UNEXPECTED (want $san / $eac)"; status=1; }
  printf '%-10s %-22s %s  [%s]\n' "$m" "$gs" "$ge" "$verdict" | sed "s/ubsan: member access within null pointer of type 'struct dllist'/ubsan: null member access/"
done
echo "step 4 (mutants x7, both builds): $(lap "$t") s"
echo "ASan start-up retries (DEADLYSIGNAL): $(cat "$B/asan_retries" 2>/dev/null | wc -l)"
[ "$status" -eq 0 ] && echo "PASS: runtime checking of B1" || echo "FAIL: runtime checking of B1"
exit $status
