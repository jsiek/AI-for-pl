# D16 Stage 2: 5b paired-seal first-try exception

Date: 2026-08-19

## Verdict

The live YZ paired-seal derivation worlds in `proof/DGG/Examples2.agda`
genuinely require the matched Z center to retain the `X⊑★` mark.  They cannot
be recalibrated to `X⊑X` without changing the intermediate type-imprecision
judgment.  Invariant (5) is not weakened; these worlds are left outside the
`WorldInvariants` companion.

The XZ calibration worlds do not use the dynamic matched-Z judgments.  Their
matched Z cell now carries `X⊑X`, and their companion proofs remain live.

## Checked sites

In `left-path-target-Z-revealed₃-YZ`, the target-only reveal step uses
`CTI2.⊑reveal²` and has the intermediate conclusion

`＇ Zᴸ ⊑ᵂ⟨ left-path-world₃-YZ ⟩ ★`.

This is witnessed by `left-path-Z-var⊑★-YZ₃`, whose only applicable variable
rule requires

`impEnvʷ left-path-world₃-YZ Z ≡ X⊑★`.

The same requirement recurs in `left-path-target-Z-revealed₈-YZ`,
`left-path-target-Z-unsealed₉-YZ`, and
`left-path-target-Z-unsealed₁₀-YZ`, through
`left-path-Z-var⊑★-YZ₄`.  These are whole-term paired-seal/reveal derivation
checkpoints, not unused calibration lemmas.

Changing the matched Z mark to `X⊑X` makes Agda reject the first witness with
`X⊑X != X⊑★`.  The tested edit was replaced by separate XZ and YZ environments:
the valid XZ worlds use `X⊑X`, while the live YZ derivation worlds retain
`X⊑★`.
