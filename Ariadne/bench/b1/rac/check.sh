#!/bin/sh
# B1 runtime checking (plan section 5 step 0, "test first").
#   From this directory:  ./check.sh [runs [seed [large]]]   (300 1 200)
# Re-runs itself inside the M0 image (../../../env/run.sh), where
# /ariadne is the Ariadne/ directory.  Steps, each timed:
#   0. generate: b1_rac.c (gen_rac.py) for b1.c and for the seven mutants
#      (../mutants.py, shared with ../check.sh);
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
runs=${1:-300} seed=${2:-1} large=${3:-200}
B1=/ariadne/bench/b1
B=build
status=0
rm -rf "$B" && mkdir -p "$B"

now() { date +%s.%N; }
lap() { python3 -c "import sys; print('%.1f' % (float(sys.argv[2]) - float(sys.argv[1])))" "$1" "$(now)"; }

MUTANTS="vacuity uaf uaf_back nullchk nullfirst nulllast noinit"
BUILTINS=rac_heap,rac_dead,rac_length,rac_nth,rac_cons,rac_tail,rac_dll
BUILTINS=$BUILTINS,rac_reach,rac_prev,rac_head
SAN="-std=c99 -g -O1 -fsanitize=address,undefined -fno-sanitize-recover=all"

# ---- 0. generate -----------------------------------------------------
t=$(now)
python3 -I "$B1/mutants.py" "$B1/b1.c" "$B/src" > /dev/null
cp "$B1/b1.c" "$B/src/orig.c"
for v in orig $MUTANTS; do
  mkdir -p "$B/$v"
  python3 -I gen_rac.py "$B/src/$v.c" "$B/$v" > "$B/$v/gen.log" ||
    { cat "$B/$v/gen.log"; echo "FAIL: gen_rac.py on $v"; exit 1; }
done
echo "step 0 (generate b1_rac.c x8): $(lap "$t") s; $(cat "$B/orig/gen.log")"

# ---- 1. sanitizers ---------------------------------------------------
san_build() {  # san_build <variant>
  gcc $SAN -I "$B/$1" -I /ariadne/plugin/share "$B/src/$1.c" rac_alloc.c \
    rac_twins.c rac_main.c -o "$B/$1/b1.asan" > "$B/$1/asan.build.log" 2>&1
}
san_run() {
  ASAN_OPTIONS=detect_leaks=1 "./$B/$1/b1.asan" "$runs" "$seed" "$large" \
    > "$B/$1/asan.log" 2>&1
}
t=$(now)
if san_build orig && san_run orig; then
  echo "PASS: ASan+UBSan build of b1.c: $(cat "$B/orig/asan.log")"
else
  echo "FAIL: ASan+UBSan build of b1.c:"; tail -20 "$B/orig/asan.log" \
    "$B/orig/asan.build.log"; status=1
fi
echo "int main(void) { return 0; }" > "$B/msan.c"
if clang -fsanitize=memory "$B/msan.c" -o "$B/msan" > "$B/msan.log" 2>&1
then
  echo "MSan available: not wired in yet"   # not the case in ariadne-m0
else
  echo "SKIP: MSan (clang -fsanitize=memory: $(grep -o 'cannot find [^ ]*msan[^ ]*' "$B/msan.log" | head -1 | sed 's|.*/||'))"
fi
echo "step 1 (sanitizers, b1.c): $(lap "$t") s"

# ---- 2. twin unit tests ----------------------------------------------
t=$(now)
if gcc $SAN -I "$B/orig" rac_twins_test.c rac_alloc.c rac_twins.c \
     -o "$B/twins_test" > "$B/twins_test.log" 2>&1 &&
   "./$B/twins_test" >> "$B/twins_test.log" 2>&1; then
  echo "PASS: $(tail -1 "$B/twins_test.log")"
else
  echo "FAIL: twin unit tests:"; cat "$B/twins_test.log"; status=1
fi
echo "step 2 (twin unit tests): $(lap "$t") s"

# ---- 3. E-ACSL -------------------------------------------------------
eacsl_build() {  # eacsl_build <variant>
  d=$B/$1
  ( cd "$d" &&
    cp ../../rac.h ../../rac_twins.h ../../rac_spec.h ../../rac_alloc.c \
       ../../rac_main.c . &&
    frama-c -e-acsl-builtins="$BUILTINS" -machdep gcc_x86_64 \
      -no-frama-c-stdlib -keep-unused-functions all \
      -cpp-extra-args="-std=c99 -D_DEFAULT_SOURCE -D__NO_CTYPE -D__FC_MACHDEP_X86_64" \
      b1_rac.c -rte -rte-initialized @all -then -print -ocode b1_rac.rte.c &&
    gcc -std=c99 -O1 -g -c -I. ../../rac_twins.c -o rac_twins.o &&
    e-acsl-gcc -c -F "-e-acsl-builtins=$BUILTINS" -l "$PWD/rac_twins.o" \
      -e "-include $PWD/rac_twins.h" -o b1_rac.frama.c -O b1_rac \
      b1_rac.rte.c ) > "$d/eacsl.build.log" 2>&1
}
eacsl_run() {
  "./$B/$1/b1_rac.e-acsl" "$runs" "$seed" "$large" > "$B/$1/eacsl.log" 2>&1
}
t=$(now)
if eacsl_build orig; then
  tb=$(lap "$t")
  t=$(now)
  if eacsl_run orig; then
    echo "PASS: E-ACSL build of b1.c: $(cat "$B/orig/eacsl.log")"
  else
    echo "FAIL: E-ACSL run of b1.c:"; tail -20 "$B/orig/eacsl.log"; status=1
  fi
  echo "step 3 (E-ACSL, b1.c): build $tb s, run $(lap "$t") s"
else
  echo "FAIL: E-ACSL build of b1.c:"; tail -30 "$B/orig/eacsl.build.log"
  exit 1
fi
python3 -I classify.py warnings "$B/orig/eacsl.build.log" > "$B/eacsl_warnings.txt"
echo "E-ACSL could not translate: $(wc -l < "$B/eacsl_warnings.txt") annotation(s) (build/eacsl_warnings.txt)"
sed 's/^/    /' "$B/eacsl_warnings.txt"

# ---- 4. mutants ------------------------------------------------------
# expect <mutant>: the sanitizer outcome and the E-ACSL outcome, as
# printed by classify.py (`-` = runs clean).
expect() {
  case "$1" in
    vacuity)   san='-'; eac='Assertion vacuity in b1' ;;
    uaf)       san='heap-use-after-free'; eac='Precondition in sglib_dllist_get_first' ;;
    uaf_back)  san='heap-use-after-free'; eac='Precondition in sglib_dllist_get_last' ;;
    nullchk)   san='SEGV'; eac='Assertion rte/mem_access in b1' ;;
    nullfirst) san='-'; eac='Postcondition heads_list in sglib_dllist_get_first' ;;
    nulllast)  san='oracle'; eac='Postcondition last_of_list in sglib_dllist_get_last' ;;
    noinit)    san='-'; eac='Precondition elem_init in sglib_dllist_add' ;;
  esac
}
t=$(now)
printf '%-10s %-22s %s\n' mutant "ASan+UBSan" "E-ACSL (first check to fire)"
for m in $MUTANTS; do
  expect "$m"
  san_build "$m" || { echo "FAIL: $m: ASan build"; status=1; continue; }
  san_run "$m"
  eacsl_build "$m" || { echo "FAIL: $m: E-ACSL build"; status=1; continue; }
  eacsl_run "$m"
  gs=$(python3 -I classify.py san "$B/$m/asan.log")
  ge=$(python3 -I classify.py eacsl "$B/$m/eacsl.log")
  verdict=ok
  [ "$gs" = "$san" ] && [ "$ge" = "$eac" ] || { verdict="UNEXPECTED (want $san / $eac)"; status=1; }
  printf '%-10s %-22s %s  [%s]\n' "$m" "$gs" "$ge" "$verdict"
done
echo "step 4 (mutants x7, both builds): $(lap "$t") s"
[ "$status" -eq 0 ] && echo "PASS: runtime checking of B1" || echo "FAIL: runtime checking of B1"
exit $status
