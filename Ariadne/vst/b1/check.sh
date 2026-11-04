#!/bin/sh
# B1a + B1b in VST.  Run from this directory:  ./check.sh
# Each step prints PASS or FAIL; the script exits non-zero on any FAIL,
# and a step whose report file is missing or empty counts as FAIL.
set -u
run=../run.sh
coqc="coqc -native-compiler no -Q . B1"
gen=../../bench/b1/b1_gen.c
status=0
mutants="bad_uaf bad_uaf_back bad_nonull bad_nullfirst bad_nulllast"

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
    && for m in $mutants; do cmp "$m.c" "$tmp/$m.c" || return 1; done \
    && rm -r "$tmp"
}
name="make_b1.py regenerates b1.c and the five bad_*.c identically"
step regen

# 2. clightgen: C -> Clight ASTs, then compile them.
clight() {
  rm -f b1.v bad_*.v ./*.vo ./*.vok ./*.vos ./*.glob \
    && "$run" clightgen -normalize b1.c bad_*.c \
    && "$run" $coqc b1.v 2> /dev/null \
    && for m in $mutants; do
         "$run" $coqc "$m.v" 2> /dev/null || return 1
       done
}
name="clightgen + coqc on b1.c and the five mutants"
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
#    if each `Fail` fails; the transcript must show 6 refusals: 2 with
#    Floyd's "no data_at for this access" message (bad_nonull), 4 with
#    "No applicable tactic" (entailer! cannot prove the call's
#    precondition in bad_uaf, bad_uaf_back, or the return value in
#    bad_nullfirst, bad_nulllast), and no other error.
bad() {
  "$run" $coqc verif_bad.v > cert/bad_coqc.txt 2>&1 \
    && "$run" coqtop -native-compiler no -Q . B1 < verif_bad.v \
         > cert/bad_transcript.txt 2>&1 \
    && [ -s cert/bad_transcript.txt ] \
    && [ "$(grep -c 'The command has indeed failed' \
              cert/bad_transcript.txt)" -eq 6 ] \
    && [ "$(grep -c 'It is not obvious how to move forward here' \
              cert/bad_transcript.txt)" -eq 2 ] \
    && [ "$(grep -A1 'The command has indeed failed' \
              cert/bad_transcript.txt \
            | grep -c '^No applicable tactic')" -eq 4 ] \
    && ! grep -q '^Error' cert/bad_transcript.txt
}
name="verif_bad.v: 2 use after free, missing NULL check, 2 NULL results refused"
step bad

exit $status
