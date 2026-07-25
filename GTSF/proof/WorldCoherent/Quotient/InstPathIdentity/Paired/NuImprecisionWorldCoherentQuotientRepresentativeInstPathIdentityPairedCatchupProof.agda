module
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupProof
  where

-- File Charter:
--   * Splits paired identity-representative quotient-inst catch-up into the
--     ordinary-down and generated-down semantic leaves.
--   * Eliminates the quotiented term constructor exhaustively.
--   * Contains no leaf implementation, postulate, hole, or fallback case.

open import QuotientedTermImprecision using
  (down⊑downᵀ; gen-down⊑gen-downᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Paired.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ)


world-coherent-quotient-representative-inst-path-identity-paired-catchup-proofᵀ :
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedIdDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedGenDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityPairedCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-paired-catchup-proofᵀ
    id-down gen-down {E≈E = E≈E} {r = r} {F≈F = F≈F}
    source-normal target-normal
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    (down⊑downᵀ d⊒ d-shape d′⊒ d′-shape
      V⊑V′ qD down-square)
    widening u-shape u′-shape up-square =
  id-down r source-normal target-normal
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d-shape d′⊒ d′-shape
    down-square V⊑V′
    widening u-shape u′-shape up-square
world-coherent-quotient-representative-inst-path-identity-paired-catchup-proofᵀ
    id-down gen-down {E≈E = E≈E} {r = r} {F≈F = F≈F}
    source-normal target-normal
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    (gen-down⊑gen-downᵀ d⊒ d-shape d′⊒ d′-shape
      V⊑V′ qD down-square)
    widening u-shape u′-shape up-square =
  gen-down r source-normal target-normal
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d-shape d′⊒ d′-shape
    down-square V⊑V′
    widening u-shape u′-shape up-square
