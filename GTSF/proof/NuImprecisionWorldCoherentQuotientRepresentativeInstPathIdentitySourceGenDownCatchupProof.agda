module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupProof
  where

-- File Charter:
--   * Implements source-only generated-down quotient-inst catch-up from the
--     ambient value dispatcher and terminal quotient catch-up capability.
--   * Reconstructs the non-vacuous source `nu` precision index using both
--     `GenSafeSource` and the explicit occurrence witness.
--   * Makes the remaining mutual-recursion dependencies visible without
--     importing their implementations or a permissive simulation module.

open import ForallPermutation using (≈∀-refl; quotientᵖ)
open import ImprecisionWf using (ν)
open import QuotientedTermImprecision using (prefix-reflⁱ)
open import
  proof.NuImprecisionWorldCoherentQuotientFinalCatchupDef
  using (WorldCoherentQuotientFinalCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentValueCatchupPrefixDef
  using (WorldCoherentLeftValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentValueCatchupPrefixProof
  using (world-coherent-left-catchup-prefix-gen-down-upᵀ)
open import proof.NuPreservation using (runtime-⟨⟩)


world-coherent-quotient-representative-inst-path-identity-source-gen-down-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentQuotientFinalCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-source-gen-down-catchup-proofᵀ
    value-catchup quotient-final {{safe = safe}}
    {pC = pC} occ r coherent exclusive wfL okN vVd noVd
    vV′ noV′ inert-d′ inert-u′ d⊒ d′⊒ V⊑V′ widening =
  world-coherent-left-catchup-prefix-gen-down-upᵀ
    quotient-final {qD = qD} prefix-reflⁱ okN
    vV′ noV′ inert-d′ inert-u′ d⊒ d′⊒ widening inner
  where
  qD = quotientᵖ ≈∀-refl (ν {{safe}} occ r) ≈∀-refl

  inner = value-catchup prefix-reflⁱ coherent exclusive wfL
    (runtime-⟨⟩ (runtime-⟨⟩ okN)) vV′ noV′ V⊑V′
