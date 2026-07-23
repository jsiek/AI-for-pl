module proof.WorldCoherent.Quotient.InstCatchup.NuImprecisionWorldCoherentQuotientInstCatchupProof where

-- File Charter:
--   * Proves that direct catch-up at exposed quotient representatives is
--     sufficient for the canonical quotient-instantiation contract.
--   * Owns only quotient elimination; permutation-aware simulation remains
--     the explicit higher-order dependency.

open import ForallPermutation using (quotientᵖ)
open import proof.WorldCoherent.Quotient.InstCatchup.NuImprecisionWorldCoherentQuotientInstCatchupDef using
  (WorldCoherentQuotientInstCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.Core.NuImprecisionWorldCoherentQuotientRepresentativeInstCatchupDef
  using (WorldCoherentQuotientRepresentativeInstCatchupᵀ)


world-coherent-quotient-inst-catchup-proofᵀ :
  WorldCoherentQuotientRepresentativeInstCatchupᵀ →
  WorldCoherentQuotientInstCatchupᵀ
world-coherent-quotient-inst-catchup-proofᵀ
    direct {qD = quotientᵖ D≈C C⊑C′ C′≈D′}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening =
  direct coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
