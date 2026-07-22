module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupProof
  where

-- File Charter:
--   * Assembles identity-path view catch-up from its paired `∀`/`∀` and
--     source-only non-vacuous `ν` semantic branches.
--   * Dispatches exhaustively on `AllImprecisionView`.
--   * Contains no branch implementation, recursive simulation, or fallback.

open import proof.ForallPermutationProperties using
  (all-paired; all-source)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupᵀ)


world-coherent-quotient-representative-inst-path-identity-view-catchup-proofᵀ :
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-view-catchup-proofᵀ
    paired source (all-paired r)
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening =
  paired coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
world-coherent-quotient-representative-inst-path-identity-view-catchup-proofᵀ
    paired source (all-source occ r)
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening =
  source coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
