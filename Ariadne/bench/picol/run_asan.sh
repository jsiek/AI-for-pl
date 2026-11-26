#!/bin/sh
# Build picol (with the Ariadne fixes) and its unit tests under gcc
# ASan/UBSan/LSan, and run the unit tests, the upstream examples and the
# regression scripts in tests/.  Prints PASS/FAIL per check; exits
# non-zero on any FAIL.
#   ./run_asan.sh          (from this directory; needs gcc)
set -u
status=0
tmp=$(mktemp -d)
cc="gcc -std=c99 -g -O0 -fsanitize=address,undefined -fno-sanitize-recover=all"
export ASAN_OPTIONS=detect_leaks=1

check() {  # name, expected stdout ("-": any), command...
  name=$1; want=$2; shift 2
  if out=$("$@" 2> "$tmp/err") && { [ "$want" = - ] || [ "$out" = "$want" ]; }
  then
    echo "PASS: $name"
  else
    echo "FAIL: $name"; head -5 "$tmp/err"; status=1
  fi
}

$cc -o "$tmp/picol" picol.c trusted.c \
  && $cc -DPICOL_MAX_ARGS_SIZE=40 -o "$tmp/picol_small" picol.c trusted.c \
  && $cc -o "$tmp/picol_test" picol_test.c trusted.c \
  && gcc -std=c99 -o "$tmp/upstream" upstream/picol.c \
  || { echo "FAIL: build"; exit 1; }
if "$tmp/picol_test" > "$tmp/out" 2>&1; then
  echo "PASS: picol_test ($(tail -1 "$tmp/out"))"
else
  echo "FAIL: picol_test"; tail -5 "$tmp/out"; status=1
fi
check "upstream/fib.tcl" - "$tmp/picol" upstream/fib.tcl
check "upstream/mandelbrot.tcl" - "$tmp/picol" upstream/mandelbrot.tcl
# A proc that redefines itself: upstream reads its freed body (ASan:
# heap-use-after-free in picolGetToken); fixed by evaluating a copy.
check "tests/proc_redefine_self.tcl" "after" \
  "$tmp/picol" tests/proc_redefine_self.tcl
# The REPL at end of input: upstream returns without freeing the
# interpreter (LSan: leaks); fixed by leaving the loop instead.
repl() { printf 'set a 1\nproc f {x} {return $x}\n' | "$tmp/$1"; }
check "REPL frees the interpreter at end of input" - repl picol
# The fixed-argument replacements for snprintf/printf (fix 3) print what
# upstream prints: the examples, and a REPL session that reaches every
# replaced message.
check "same output as upstream: fib.tcl" \
  "$("$tmp/upstream" upstream/fib.tcl)" "$tmp/picol" upstream/fib.tcl
check "same output as upstream: mandelbrot.tcl" \
  "$("$tmp/upstream" upstream/mandelbrot.tcl)" "$tmp/picol" upstream/mandelbrot.tcl
check "same output as upstream: REPL on tests/messages.tcl" \
  "$("$tmp/upstream" < tests/messages.tcl)" sh -c "\"$tmp/picol\" < tests/messages.tcl"
# The bound on a command's argument size (fix 6), lowered to 40 bytes:
# 4+2+31 bytes pass, 4+2+41 fail instead of overflowing.
check "tests/args_limit.tcl (bound 40)" \
  "$(printf '012345678901234567890123456789\nCommand too long')" \
  "$tmp/picol_small" tests/args_limit.tcl
rm -r "$tmp"
exit $status
