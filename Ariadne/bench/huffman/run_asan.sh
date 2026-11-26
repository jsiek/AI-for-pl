#!/bin/sh
# Build huffcode (huffman.c + huffcode.c from SRC, default upstream/)
# under gcc ASan/UBSan/LSan and run upstream's run_tests.sh, round trips
# on edge inputs in file mode and memory mode (-m), and the reproducers
# of bugs B4-B8 in README.md (the round trips show B1-B3).  Prints
# PASS/FAIL per check, with the sanitizer's or assertion's message for
# each FAIL; exits non-zero on any FAIL.  On upstream (2026-11-26):
# 7 PASS, 11 FAIL, as README.md lists.
#   ./run_asan.sh [SRC]    (from this directory; needs gcc and python3)
set -u
src=${1:-upstream}
status=0
tmp=$(mktemp -d)
# A sanitizer report exits 23, so it is never mistaken for huffcode's
# own error status 1 (which the decompress tests expect).
export ASAN_OPTIONS=detect_leaks=1:exitcode=23
export UBSAN_OPTIONS=print_stacktrace=1:exitcode=23
export LSAN_OPTIONS=exitcode=23
cc="gcc -std=c11 -D_POSIX_C_SOURCE=2 -g -O0 -fno-omit-frame-pointer
    -fsanitize=address,undefined -fno-sanitize-recover=all"
# huffcode_nn: without UBSan's nonnull check (bug B1), to see whether the
# rest of upstream's tests pass.  huffcode_plain: no sanitizers (B8).
$cc -o "$tmp/huffcode" "$src/huffman.c" "$src/huffcode.c" \
  && $cc -fno-sanitize=nonnull-attribute -o "$tmp/huffcode_nn" \
       "$src/huffman.c" "$src/huffcode.c" \
  && gcc -std=c11 -D_POSIX_C_SOURCE=2 -g -O0 -o "$tmp/huffcode_plain" \
       "$src/huffman.c" "$src/huffcode.c" \
  || { echo "FAIL: build"; exit 1; }
hc=$tmp/huffcode

report() {  # the sanitizer's or assertion's message in $tmp/err, if any
  grep -E 'ERROR|runtime error|Assertion|double free' "$tmp/err" \
    | head -2 | sed 's/^/    /'
}
pass() { echo "PASS: $1"; }
fail() { echo "FAIL: $1"; report; status=1; }

# Inputs: upstream's test files plus edge cases.
mkdir "$tmp/in"
cp -r "$src/test_data" "$src/run_tests.sh" "$tmp/"
python3 - "$tmp/in" <<'EOF'
import os, random, sys
d = sys.argv[1]
def w(name, data): open(os.path.join(d, name), "wb").write(data)
w("empty", b"")
w("one_byte", b"x")
w("all_256", bytes(range(256)))
w("repeat_4096", b"a" * 4096)
random.seed(1)
w("random_1M", bytes(random.getrandbits(8) for _ in range(1 << 20)))
# Two symbols, 2 MiB: decoding it in memory mode needs a 2 MiB malloc.
w("ab_2M", b"ab" * (1 << 20))
# A code table that file mode rejects: 'a' has code 0 (1 bit), 'b' has
# code 000 (3 bits), so b's path runs through a's leaf.
w("leaf_on_path.huf", bytes([0,0,0,2, 0,0,0,1, 0x61,1,0, 0x62,3,0, 0]))
EOF

# 1. Upstream's own tests (round trips of test_data/, and the issue-2
#    fuzzer files must fail cleanly with status 1), run in a copy.
upstream_tests() {  # binary, label
  if (cd "$tmp" && ./run_tests.sh --huffcode "$1") > "$tmp/out" 2> "$tmp/err"
  then pass "$2 ($(tail -1 "$tmp/out"))"
  else tail -2 "$tmp/out" | sed 's/^/    /'; fail "$2"
  fi
}
upstream_tests "$hc" "upstream run_tests.sh"
upstream_tests "$tmp/huffcode_nn" "upstream run_tests.sh, nonnull check off"

# 2. Round trips: encode then decode (flags: '' file mode, -m memory mode).
roundtrip() {  # mode-flag, input-file
  f=$tmp/in/$2; label="round trip $2 (${1:-file mode})"
  if "$hc" $1 -i "$f" -o "$f.huf$1" 2> "$tmp/err" \
     && "$hc" $1 -d -i "$f.huf$1" -o "$f.out$1" 2> "$tmp/err" \
     && cmp -s "$f" "$f.out$1"
  then pass "$label"
  else fail "$label"
  fi
}
for x in empty one_byte all_256 repeat_4096 random_1M; do
  roundtrip "" $x
  roundtrip -m $x
done

# 3. Bug reproducers (README.md, "Bugs").
# B4: memory-mode decode follows a leaf's union as child pointers.
"$hc" -d -i "$tmp/in/leaf_on_path.huf" -o "$tmp/o1" 2> "$tmp/err"
[ $? = 1 ] && pass "file-mode decode rejects leaf_on_path.huf" \
  || fail "file-mode decode rejects leaf_on_path.huf"
"$hc" -m -d -i "$tmp/in/leaf_on_path.huf" -o "$tmp/o2" 2> "$tmp/err"
[ $? = 1 ] && pass "memory-mode decode rejects leaf_on_path.huf" \
  || fail "memory-mode decode rejects leaf_on_path.huf"
# B5: the issue-2 fuzzer files in memory mode (file mode: run_tests.sh).
n=0; bad=""
for f in "$tmp"/test_data/reported_issues/issue2/*; do
  "$hc" -m -d -i "$f" -o "$tmp/o3" 2> "$tmp/err"
  [ $? = 1 ] || { n=$((n+1)); bad=$f; cp "$tmp/err" "$tmp/err.keep"; }
done
if [ $n = 0 ]; then pass "memory-mode decode rejects the issue-2 files"
else cp "$tmp/err.keep" "$tmp/err"
     fail "memory-mode decode rejects the issue-2 files ($n bad; last: $(basename "$bad"))"
fi
# B6: memory-mode decode does not check malloc; make a 2 MiB malloc fail.
"$hc" -i "$tmp/in/ab_2M" -o "$tmp/in/ab_2M.huf" 2> "$tmp/err"
if ASAN_OPTIONS=$ASAN_OPTIONS:allocator_may_return_null=1:max_allocation_size_mb=1 \
   "$hc" -m -d -i "$tmp/in/ab_2M.huf" -o "$tmp/o4" 2> "$tmp/err" \
   || [ $? = 1 ]
then pass "memory-mode decode survives a failed malloc"
else fail "memory-mode decode survives a failed malloc"
fi
# B7: encoding from a pipe: rewind fails, the second pass reads nothing.
printf 'ab' | "$hc" > "$tmp/pipe.huf" 2> "$tmp/err"
if [ "$("$hc" -d < "$tmp/pipe.huf" 2>> "$tmp/err")" = ab ]
then pass "round trip of 'ab' through a pipe"
else fail "round trip of 'ab' through a pipe (decodes to '')"
fi
# B8: -m on a directory: fread fails without EOF, so the read loop grows
# the buffer until `len` wraps to 0; realloc(buf, 0) frees buf and
# returns NULL, and buf is freed again.  Plain build: under ASan each
# realloc copies the buffer, so it is not run there.
mkdir "$tmp/dir"
timeout 60 "$tmp/huffcode_plain" -m -i "$tmp/dir" -o "$tmp/o5" 2> "$tmp/err"
rc=$?
if [ $rc = 1 ]; then pass "-m on a directory fails cleanly (plain build)"
else echo "    exit status $rc"
     fail "-m on a directory fails cleanly (plain build)"
fi
rm -r "$tmp"
exit $status
