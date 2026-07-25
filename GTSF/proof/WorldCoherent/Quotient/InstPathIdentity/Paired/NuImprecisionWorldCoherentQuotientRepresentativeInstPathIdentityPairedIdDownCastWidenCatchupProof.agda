module
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupProof
  where

-- File Charter:
--   * Implements the paired ordinary-down/general-widening quotient-inst
--     residual from value-prefix and terminal quotient catch-up.
--   * Reconstructs the exact identity-representative quotient index and
--     widening pair without assuming cast-mode compatibility with the
--     ambient imprecision context.
--   * Exposes the genuine mutual-SCC dependencies and imports no recursive
--     implementation, permissive option, or broad simulation module.

open import ForallPermutation using (≈∀-refl; quotientᵖ)
open import ImprecisionWf using (∀ⁱ_)
open import QuotientedTermImprecision using
  (prefix-reflⁱ; quotient-cast-widening)
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalCatchupDef
  using (WorldCoherentQuotientFinalCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef
  using (WorldCoherentLeftValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixProof
  using (world-coherent-left-catchup-prefix-down-upᵀ)
open import proof.DGG.Core.NuPreservation using (runtime-⟨⟩)


world-coherent-quotient-representative-inst-path-identity-paired-id-down-cast-widen-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentQuotientFinalCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-paired-id-down-cast-widen-catchup-proofᵀ
    value-catchup quotient-final
    {E≈E = E≈E} {pC = pC} {F≈F = F≈F} {pA = pA}
    r coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    d⊒ d-shape d′⊒ d′-shape down-square V⊑V′
    mode seal★ u⊑ mode′ seal★′ u′⊑
    u-shape u′-shape up-square =
  world-coherent-left-catchup-prefix-down-upᵀ
    quotient-final {pC = pC} {qD = qD} {pA = pA}
    prefix-reflⁱ okN vV′ noV′ inert-d′ inert-u′
    d⊒ d-shape d′⊒ d′-shape down-square
    widening u-shape u′-shape up-square inner
  where
  qD = quotientᵖ E≈E (∀ⁱ r) F≈F

  widening = quotient-cast-widening
    mode seal★ u⊑ mode′ seal★′ u′⊑

  inner = value-catchup prefix-reflⁱ coherent exclusive wfL
    (runtime-⟨⟩ (runtime-⟨⟩ okN)) vV′ noV′ V⊑V′
