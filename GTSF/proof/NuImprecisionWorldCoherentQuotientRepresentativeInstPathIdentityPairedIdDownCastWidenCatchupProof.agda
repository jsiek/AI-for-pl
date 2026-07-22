module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupProof
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
  proof.NuImprecisionWorldCoherentQuotientFinalCatchupDef
  using (WorldCoherentQuotientFinalCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentValueCatchupPrefixDef
  using (WorldCoherentLeftValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentValueCatchupPrefixProof
  using (world-coherent-left-catchup-prefix-down-upᵀ)
open import proof.NuPreservation using (runtime-⟨⟩)


world-coherent-quotient-representative-inst-path-identity-paired-id-down-cast-widen-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentQuotientFinalCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCastWidenCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-paired-id-down-cast-widen-catchup-proofᵀ
    value-catchup quotient-final {pC = pC}
    r coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d′⊒ V⊑V′
    mode seal★ u⊑ mode′ seal★′ u′⊑ =
  world-coherent-left-catchup-prefix-down-upᵀ
    quotient-final {qD = qD} prefix-reflⁱ okN
    vV′ noV′ inert-d′ inert-u′ d⊒ d′⊒ widening inner
  where
  qD = quotientᵖ ≈∀-refl (∀ⁱ r) ≈∀-refl

  widening = quotient-cast-widening
    mode seal★ u⊑ mode′ seal★′ u′⊑

  inner = value-catchup prefix-reflⁱ coherent exclusive wfL
    (runtime-⟨⟩ (runtime-⟨⟩ okN)) vV′ noV′ V⊑V′
