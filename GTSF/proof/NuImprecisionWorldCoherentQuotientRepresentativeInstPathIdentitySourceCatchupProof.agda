module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupProof
  where

-- File Charter:
--   * Splits non-vacuous source-only identity-representative quotient-inst
--     catch-up into ordinary-down and generated-down semantic leaves.
--   * Eliminates the quotiented term constructor exhaustively while retaining
--     the implicit `GenSafeSource` and occurrence witnesses.
--   * Contains no leaf implementation, postulate, hole, or fallback case.

open import QuotientedTermImprecision using
  (down⊑downᵀ; gen-down⊑gen-downᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ)


world-coherent-quotient-representative-inst-path-identity-source-catchup-proofᵀ :
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceGenDownCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-source-catchup-proofᵀ
    id-down gen-down {{safe = safe}} {occ = occ} {r = r}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    (down⊑downᵀ d⊒ d′⊒ V⊑V′ qD) widening =
  id-down {{safe}} occ r
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d′⊒ V⊑V′ widening
world-coherent-quotient-representative-inst-path-identity-source-catchup-proofᵀ
    id-down gen-down {{safe = safe}} {occ = occ} {r = r}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    (gen-down⊑gen-downᵀ d⊒ d′⊒ V⊑V′ qD) widening =
  gen-down {{safe}} occ r
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d′⊒ V⊑V′ widening
