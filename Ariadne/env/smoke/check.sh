#!/bin/sh
# M0 smoke test for the Ariadne toolchain image.  Run from this directory:
#   ./check.sh
# Each step prints PASS or FAIL; the script exits non-zero on any FAIL.
set -u
run=../run.sh
why3lib=/home/rocq/.opam/4.14.2/lib/why3/coq
status=0

step() {
  if "$@"; then echo "PASS: $name"; else echo "FAIL: $name"; status=1; fi
}

wp_all_proved() {
  "$run" frama-c -wp -wp-rte -wp-model Typed -wp-prover alt-ergo,z3,coq \
    -wp-interactive batch -wp-session /work/"$1" "$2" > "$1.log" 2>&1
  grep -E "Proved goals: +([0-9]+) / \1$" "$1.log" > /dev/null
}

# 1. WP round trip: Qed + Alt-Ergo + one Coq script (sum_nonneg).
name="WP round trip, all goals proved (swap.c)"
step wp_all_proved session swap.c

# 2. Certificate: compile the Coq script and re-check it with coqchk.
certify() {
  rm -rf cert && mkdir cert \
    && cp session/interactive/lemma_sum_nonneg.v cert/ \
    && "$run" coqc -R "$why3lib" Why3 -Q cert Goals \
         cert/lemma_sum_nonneg.v \
    && "$run" coqchk -silent -o -R "$why3lib" Why3 -Q cert Goals \
         Goals.lemma_sum_nonneg > cert/coqchk.txt 2>&1 \
    && grep -q "CONTEXT SUMMARY" cert/coqchk.txt
}
name="coqchk accepts the certificate (axioms in cert/coqchk.txt)"
step certify

# 3. CoqHammer with external ATPs (Vampire, Eprover) and sauto.
name="CoqHammer (hammer_check.v)"
step "$run" coqc hammer_check.v

# 4. Petanque drives a WP-generated goal tactic by tactic.
petanque() {
  cp session/interactive/lemma_sum_nonneg.v pet/ && python3 -I pet_check.py
}
name="Petanque (pet_check.py)"
step petanque

# 5. Known hole: a non-terminating recursive ACSL definition is exported
#    as an inconsistent axiom.  This step PASSES when the hole is still
#    present, so the guardrail of plan.md section 7 stays necessary.
name="known hole still present: bad_def.c lemma proved from bad axiom"
step wp_all_proved session_bad bad_def.c

exit $status
