module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupProof
  where

-- File Charter:
--   * Splits paired identity-representative quotient-inst catch-up into the
--     ordinary-down and generated-down semantic leaves.
--   * Eliminates the quotiented term constructor exhaustively.
--   * Contains no leaf implementation, postulate, hole, or fallback case.

open import QuotientedTermImprecision using
  (down⊑downᵀ; gen-down⊑gen-downᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ)


world-coherent-quotient-representative-inst-path-identity-paired-catchup-proofᵀ :
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-paired-catchup-proofᵀ
    id-down gen-down {r = r}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    (down⊑downᵀ d⊒ d′⊒ V⊑V′ qD) widening =
  id-down r coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d′⊒ V⊑V′ widening
world-coherent-quotient-representative-inst-path-identity-paired-catchup-proofᵀ
    id-down gen-down {r = r}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    (gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD) widening =
  gen-down r coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d′⊒ V⊑V′ widening
