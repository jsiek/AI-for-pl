#!/bin/sh
# SMTCoq on the VST image.  Run from this directory:  ./check.sh
# Each step prints PASS or FAIL; the script exits non-zero on any FAIL.
set -u
run=../run.sh
status=0

step() {
  if "$@"; then echo "PASS: $name"; else echo "FAIL: $name"; status=1; fi
}

rm -rf out
"$run" sh run_tests.sh

# 1. Small goals over Z, bool, nat, lists: which tactic proves which.
name="smoke.v: probe results as in expected_smoke.txt"
step diff -u expected_smoke.txt out/smoke.txt

# 2. B1 side goals: SMTCoq vs lia / rep_lia / list_solve.
name="b1_side.v: probe results as in expected_b1_side.txt"
step diff -u expected_b1_side.txt out/b1_side.txt

# 3. SMTCoq proofs pass Qed; Print Assumptions as recorded.
assumptions() {
  grep -q '^proved coqc exit 0$' out/status.txt \
    && grep -vE '^(File |Warning: Bytecode|\[bytecode)' out/proved.log \
         > out/assumptions.txt \
    && diff -u expected_assumptions.txt out/assumptions.txt
}
name="proved.v: Qed; assumptions as in expected_assumptions.txt"
step assumptions

exit $status
