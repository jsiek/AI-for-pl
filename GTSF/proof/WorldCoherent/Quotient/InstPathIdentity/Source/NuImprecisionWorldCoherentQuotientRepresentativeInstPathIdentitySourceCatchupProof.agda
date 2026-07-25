module
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupProof
  where

-- File Charter:
--   * Splits non-vacuous source-only identity-representative quotient-inst
--     catch-up into ordinary-down and generated-down semantic leaves.
--   * Eliminates the quotiented term constructor exhaustively while retaining
--     the explicit `NonVar` and occurrence witnesses.
--   * Contains no leaf implementation, postulate, hole, or fallback case.

open import QuotientedTermImprecision using
  (down⊑downᵀ; gen-down⊑gen-downᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ)


world-coherent-quotient-representative-inst-path-identity-source-catchup-proofᵀ :
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-source-catchup-proofᵀ
    id-down gen-down {E≈E = E≈E} {{safe = safe}}
    {occ = occ} {r = r} {C′≈C′ = C′≈C′}
    source-normal target-normal
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    (down⊑downᵀ d⊒ d-shape d′⊒ d′-shape
      V⊑V′ qD down-square)
    widening u-shape u′-shape up-square =
  id-down {{safe}} occ r
    source-normal target-normal
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d-shape d′⊒ d′-shape
    down-square V⊑V′
    widening u-shape u′-shape up-square
world-coherent-quotient-representative-inst-path-identity-source-catchup-proofᵀ
    id-down gen-down {E≈E = E≈E} {{safe = safe}}
    {occ = occ} {r = r} {C′≈C′ = C′≈C′}
    source-normal target-normal
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    (gen-down⊑gen-downᵀ d⊒ d-shape d′⊒ d′-shape
      V⊑V′ qD down-square)
    widening u-shape u′-shape up-square =
  gen-down {{safe}} occ r
    source-normal target-normal
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d-shape d′⊒ d′-shape
    down-square V⊑V′
    widening u-shape u′-shape up-square
