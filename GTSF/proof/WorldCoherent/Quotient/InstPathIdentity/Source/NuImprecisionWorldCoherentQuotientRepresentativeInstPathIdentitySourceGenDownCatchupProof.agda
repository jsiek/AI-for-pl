module
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupProof
  where

-- File Charter:
--   * Implements source-only generated-down quotient-inst catch-up from the
--     ambient value dispatcher and terminal quotient catch-up capability.
--   * Reconstructs the non-vacuous source `nu` precision index using both
--     `NonVar` and the explicit occurrence witness.
--   * Makes the remaining mutual-recursion dependencies visible without
--     importing their implementations or a permissive simulation module.

open import ForallPermutation using (≈∀-refl; quotientᵖ)
open import ImprecisionWf using (ν)
open import QuotientedTermImprecision using (prefix-reflⁱ)
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalCatchupDef
  using (WorldCoherentQuotientFinalCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef
  using (WorldCoherentLeftValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixProof
  using (world-coherent-left-catchup-prefix-gen-down-upᵀ)
open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩)


world-coherent-quotient-representative-inst-path-identity-source-gen-down-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentQuotientFinalCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-source-gen-down-catchup-proofᵀ
    value-catchup quotient-final
    {E≈E = E≈E} {{safe = safe}}
    {pC = pC} {T≈T = T≈T}
    {pA = pA}
    occ r source-normal target-normal
    coherent exclusive wfL okN vVd noVd
    vV′ noV′ inert-d′ inert-u′
    d⊒ d-shape d′⊒ d′-shape down-square V⊑V′
    widening u-shape u′-shape up-square =
  world-coherent-left-catchup-prefix-gen-down-upᵀ
    quotient-final {pC = pC} {qD = qD} {pA = pA}
    prefix-reflⁱ okN vV′ noV′ inert-d′ inert-u′
    d⊒ d-shape d′⊒ d′-shape down-square
    widening u-shape u′-shape up-square inner
  where
  qD = quotientᵖ E≈E (ν safe occ r) T≈T

  inner = value-catchup prefix-reflⁱ coherent exclusive wfL
    (runtime-⟨⟩ (runtime-⟨⟩ okN)) vV′ noV′ V⊑V′
