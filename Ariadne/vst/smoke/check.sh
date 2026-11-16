#!/bin/sh
# VST smoke test for the Ariadne VST image.  Run from this directory:
#   ./check.sh            (add COQCHK=1 to also re-check with coqchk)
# Each step prints PASS or FAIL; the script exits non-zero on any FAIL.
set -u
run=../run.sh
coqc="coqc -native-compiler no -Q . Smoke"
status=0

step() {
  if "$@"; then echo "PASS: $name"; else echo "FAIL: $name"; status=1; fi
}

# 1. clightgen: C -> Clight ASTs (good.v, bad.v), then compile them.
clight() {
  rm -f good.v bad.v ./*.vo ./*.vok ./*.vos ./*.glob \
    && "$run" clightgen -normalize good.c bad.c \
    && "$run" $coqc good.v 2> /dev/null \
    && "$run" $coqc bad.v 2> /dev/null
}
name="clightgen + coqc on good.c and bad.c"
step clight

# 2. The good program is verified: semax_body for each function and
#    semax_prog for the whole program.  The Print Assumptions output
#    must equal the recorded allow-list exactly.
good() {
  mkdir -p cert \
    && "$run" $coqc verif_good.v > cert/assumptions.txt 2>&1 \
    && diff -u expected_assumptions.txt cert/assumptions.txt
}
name="verif_good.v: prog_correct proved; assumptions as expected"
step good

# 3. The bad program: every bad step is refused.  verif_bad.v compiles
#    only if each `Fail` fails; the transcript must show that the two
#    accesses after free failed for the expected reason (no data_at
#    for the freed cell) and that the double free's precondition was
#    not provable.
bad() {
  "$run" $coqc verif_bad.v \
    && "$run" coqtop -native-compiler no -Q . Smoke < verif_bad.v \
         > cert/bad_transcript.txt 2>&1 \
    && [ "$(grep -c 'The command has indeed failed' \
              cert/bad_transcript.txt)" -eq 4 ] \
    && [ "$(grep -c 'It is not obvious how to move forward here' \
              cert/bad_transcript.txt)" -eq 2 ] \
    && ! grep -q '^Error' cert/bad_transcript.txt
}
name="verif_bad.v: use after free, write through alias, double free refused"
step bad

# 4. Petanque drives the good proof step by step and sees the refusal
#    of the access after free.
name="Petanque (pet_check.py)"
step python3 -I pet_check.py

# 5. Optional: re-check the certificate and all of VST with coqchk.
if [ "${COQCHK:-0}" = 1 ]; then
  chk() {
    "$run" coqchk -silent -o -Q . Smoke Smoke.verif_good \
      > cert/coqchk.txt 2>&1 \
      && grep -q "CONTEXT SUMMARY" cert/coqchk.txt
  }
  name="coqchk accepts verif_good (axioms in cert/coqchk.txt)"
  step chk
fi

exit $status
