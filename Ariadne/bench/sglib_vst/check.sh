#!/bin/sh
# Compile check of the stage-1 spec (type check only; no proofs yet).
# Run from this directory:  ./check.sh
# Each step prints PASS or FAIL; the script exits non-zero on any FAIL.
set -u
run=../../vst/run.sh
coqc="coqc -native-compiler no -Q . SglibVST"
status=0

step() {
  if "$@"; then echo "PASS: $name"; else echo "FAIL: $name"; status=1; fi
}

# 1. dllist.c is what make_dllist.py produces from ../b1/b1_gen.c (the
#    script asserts that every copied sglib piece is verbatim).
regen() {
  tmp=$(mktemp -d) \
    && cp dllist.c "$tmp"/dllist.c.orig \
    && python3 -I make_dllist.py \
    && cmp dllist.c "$tmp"/dllist.c.orig \
    && rm -r "$tmp"
}
name="make_dllist.py regenerates dllist.c identically"
step regen

# 2. clightgen: C -> Clight AST, then compile it.
clight() {
  rm -f dllist.v ./*.vo ./*.vok ./*.vos ./*.glob \
    && "$run" clightgen -normalize dllist.c \
    && "$run" $coqc dllist.v 2> /dev/null
}
name="clightgen + coqc on dllist.c"
step clight

# 3. The funspecs and the six semax_body statements elaborate.
spec() {
  "$run" $coqc spec_dllist.v
}
name="coqc spec_dllist.v (funspecs type-check against dllist.v)"
step spec

# 4. Exactly the six body lemmas are Admitted; no other admit or axiom.
lint() {
  [ "$(grep -c '^Admitted\.$' spec_dllist.v)" -eq 6 ] \
    && ! grep -nE '\b(admit|Axiom|Parameter|Conjecture)\b' spec_dllist.v
}
name="spec_dllist.v: 6 Admitted body lemmas, no other admit/axiom"
step lint

# 5. The affinity probe: VST does not let a function drop a data_at or a
#    malloc_token at return unless its postcondition has TT
#    (affine_probe/verif_probe.v compiles only if that is so).
affine() {
  (cd affine_probe \
    && rm -f probe.v ./*.vo ./*.vok ./*.vos ./*.glob \
    && "../$run" clightgen -normalize probe.c \
    && "../$run" coqc -native-compiler no -Q . Probe probe.v 2> /dev/null \
    && "../$run" coqc -native-compiler no -Q . Probe verif_probe.v \
         2> /dev/null)
}
name="affine_probe: memory is dropped only through TT"
step affine

# 6. Leak freedom (owner, R10): no TT and no existential over mpred in
#    any postcondition of the public spec, helpers unfolded.
postlint() {
  python3 -I lint/post_lint.py spec_dllist.v
}
name="post_lint: spec_dllist.v's postconditions are leak-free"
step postlint

# 7. The lint's own tests, and the lint on a real file with TT: it must
#    flag exactly the probe's two TT postconditions.
lintcheck() {
  python3 -I lint/test_post_lint.py 2> /dev/null || return 1
  out=$(python3 -I lint/post_lint.py affine_probe/verif_probe.v)
  rc=$?
  [ "$rc" -eq 1 ] \
    && [ "$(printf '%s\n' "$out" | grep -c '^FAIL: drop_.*_TT_spec: TT')" \
         -eq 2 ]
}
name="post_lint: unit tests pass; flags the probe's 2 TT postconditions"
step lintcheck

# 8. The frozen spec (owner's approval, 2026-11-17): SPEC.md and
#    spec_dllist.v hash to the recorded digest, which SPEC.md states.
#    A change to the frozen spec is a public change (owner's approval).
frozen_digest=ee6043a2f971a9f6
frozen() {
  [ "$(python3 -I frozen_digest.py)" = "$frozen_digest" ] \
    && [ "$(python3 -I frozen_digest.py --stated)" = "$frozen_digest" ]
}
name="frozen spec digest $frozen_digest (SPEC.md + spec_dllist.v)"
step frozen

exit $status
