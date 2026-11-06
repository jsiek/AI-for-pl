#!/bin/sh
# Expand the sglib macros of gen_in.c into readable C (b1_gen.c), so the
# generated functions can be annotated (plan Q4: annotate the
# preprocessed code).  stub/assert.h is empty so `assert(...)` stays as
# text and Frama-C's own <assert.h> handles it later.
#   usage (from this directory): ./gen.sh
#   sglib.h is used with B1's verification refactor #1 (CHANGES.md):
#   refactor/it_next_calls.py writes the refactored copy; the vendored
#   file is not modified.
set -eu
../../env/run.sh sh -c '
  set -e
  mkdir -p /tmp/sglib_r
  python3 -I refactor/it_next_calls.py /ariadne/bench/sglib/sglib.h \
    /tmp/sglib_r/sglib.h
  cpp -P -nostdinc -I stub -I /tmp/sglib_r gen_in.c > /tmp/b1.i
  clang-format-14 --style="{BasedOnStyle: LLVM, ColumnLimit: 79}" /tmp/b1.i
' > b1_gen.c.tmp
mv b1_gen.c.tmp b1_gen.c
echo "wrote b1_gen.c ($(wc -l < b1_gen.c) lines)"
