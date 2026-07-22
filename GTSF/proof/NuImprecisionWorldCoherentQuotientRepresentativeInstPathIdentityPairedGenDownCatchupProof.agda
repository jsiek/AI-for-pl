module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupProof
  where

-- File Charter:
--   * Implements paired generated-down quotient-inst catch-up from the
--     ambient value dispatcher and terminal quotient catch-up capability.
--   * Reconstructs the identity-representative quotient index explicitly.
--   * Makes the remaining mutual-recursion dependencies visible without
--     importing their implementations or a permissive simulation module.

open import ForallPermutation using (≈∀-refl; quotientᵖ)
open import ImprecisionWf using (∀ⁱ_)
open import QuotientedTermImprecision using (prefix-reflⁱ)
open import
  proof.NuImprecisionWorldCoherentQuotientFinalCatchupDef
  using (WorldCoherentQuotientFinalCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentValueCatchupPrefixDef
  using (WorldCoherentLeftValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentValueCatchupPrefixProof
  using (world-coherent-left-catchup-prefix-gen-down-upᵀ)
open import proof.NuPreservation using (runtime-⟨⟩)


world-coherent-quotient-representative-inst-path-identity-paired-gen-down-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentQuotientFinalCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-paired-gen-down-catchup-proofᵀ
    value-catchup quotient-final {pC = pC}
    r coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d′⊒ V⊑V′ widening =
  world-coherent-left-catchup-prefix-gen-down-upᵀ
    quotient-final {qD = qD} prefix-reflⁱ okN
    vV′ noV′ inert-d′ inert-u′ d⊒ d′⊒ widening inner
  where
  qD = quotientᵖ ≈∀-refl (∀ⁱ r) ≈∀-refl

  inner = value-catchup prefix-reflⁱ coherent exclusive wfL
    (runtime-⟨⟩ (runtime-⟨⟩ okN)) vV′ noV′ V⊑V′
