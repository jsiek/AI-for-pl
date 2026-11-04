#!/bin/sh
# Expand the sglib macros of gen_in.c into readable C (b1_gen.c), so the
# generated functions can be annotated (plan Q4: annotate the
# preprocessed code).  stub/assert.h is empty so `assert(...)` stays as
# text and Frama-C's own <assert.h> handles it later.
#   usage (from this directory): ./gen.sh
set -eu
../../env/run.sh sh -c '
  set -e
  cpp -P -nostdinc -I stub -I /ariadne/bench/sglib gen_in.c > /tmp/b1.i
  clang-format-14 --style="{BasedOnStyle: LLVM, ColumnLimit: 79}" /tmp/b1.i
' > b1_gen.c.tmp
mv b1_gen.c.tmp b1_gen.c
echo "wrote b1_gen.c ($(wc -l < b1_gen.c) lines)"
