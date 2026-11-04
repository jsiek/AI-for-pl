#!/bin/sh
# B1a in VST.  Run from this directory:  ./check.sh
# Each step prints PASS or FAIL; the script exits non-zero on any FAIL,
# and a step whose report file is missing or empty counts as FAIL.
set -u
run=../run.sh
coqc="coqc -native-compiler no -Q . B1"
gen=../../bench/b1/b1_gen.c
status=0

step() {
  if "$@"; then echo "PASS: $name"; else echo "FAIL: $name"; status=1; fi
}

mkdir -p cert
rm -f cert/*

# 1. The C files are what make_b1.py produces from b1_gen.c (the script
#    asserts that every copied sglib piece is verbatim from b1_gen.c).
regen() {
  tmp=$(mktemp -d) \
    && cp make_b1.py "$tmp"/ \
    && python3 -I "$tmp"/make_b1.py "$gen" "$tmp"/b1.c \
    && cmp b1.c "$tmp"/b1.c \
    && cmp bad_uaf.c "$tmp"/bad_uaf.c \
    && cmp bad_nonull.c "$tmp"/bad_nonull.c \
    && rm -r "$tmp"
}
name="make_b1.py regenerates b1.c, bad_uaf.c, bad_nonull.c identically"
step regen

# 2. clightgen: C -> Clight ASTs, then compile them.
clight() {
  rm -f b1.v bad_uaf.v bad_nonull.v ./*.vo ./*.vok ./*.vos ./*.glob \
    && "$run" clightgen -normalize b1.c bad_uaf.c bad_nonull.c \
    && "$run" $coqc b1.v 2> /dev/null \
    && "$run" $coqc bad_uaf.v 2> /dev/null \
    && "$run" $coqc bad_nonull.v 2> /dev/null
}
name="clightgen + coqc on b1.c and the two mutants"
step clight

# 3. No admits or new axioms in the proof files.
lint() {
  ! grep -nE '\b(Admitted|admit|Axiom|Parameter|Conjecture)\b' \
      verif_b1.v verif_bad.v
}
name="no Admitted/admit/Axiom/Parameter in verif_b1.v, verif_bad.v"
step lint

# 4. The program is verified: semax_body for every function and
#    semax_prog for the whole program.  Print Assumptions must equal the
#    recorded allow-list exactly.
good() {
  "$run" $coqc verif_b1.v > cert/assumptions.txt 2>&1 \
    && [ -s cert/assumptions.txt ] \
    && head -1 cert/assumptions.txt | grep -qx 'Axioms:' \
    && diff -u expected_assumptions.txt cert/assumptions.txt
}
name="verif_b1.v: prog_correct proved; assumptions as expected"
step good

# 5. The mutants: every bad step is refused.  verif_bad.v compiles only
#    if each `Fail` fails; the transcript must show 4 refusals, 3 of them
#    Floyd's "no data_at for this access" message, and no other error.
bad() {
  "$run" $coqc verif_bad.v > cert/bad_coqc.txt 2>&1 \
    && "$run" coqtop -native-compiler no -Q . B1 < verif_bad.v \
         > cert/bad_transcript.txt 2>&1 \
    && [ -s cert/bad_transcript.txt ] \
    && [ "$(grep -c 'The command has indeed failed' \
              cert/bad_transcript.txt)" -eq 4 ] \
    && [ "$(grep -c 'It is not obvious how to move forward here' \
              cert/bad_transcript.txt)" -eq 3 ] \
    && ! grep -q '^Error' cert/bad_transcript.txt
}
name="verif_bad.v: use after free and missing NULL check refused"
step bad

exit $status
