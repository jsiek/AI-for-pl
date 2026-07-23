module
  proof.WorldCoherent.Quotient.InstPathIdentity.Core.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityCatchupProof
  where

-- File Charter:
--   * Reduces identity-path representative-inst catch-up to the exact
--     paired-versus-source-only view of its universal representative.
--   * Obtains that view by dependent elimination of the source `inst`
--     widening; no quotient-to-ordinary conversion is assumed.
--   * Contains no view-case semantics or recursive simulation implementation.

import Coercions as C
open import Data.Product using (_,_)
import NarrowWiden as NW
open import proof.Core.Permutation.ForallPermutationProperties using
  (all-imprecision-view)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Core.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.View.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupᵀ)


world-coherent-quotient-representative-inst-path-identity-catchup-proofᵀ :
  WorldCoherentQuotientRepresentativeInstPathIdentityViewCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentityCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-catchup-proofᵀ
    view {C⊑C′ = C⊑C′}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down
    widening@(quotient-id-widening
      (C.cast-inst hB occ s⊢ , NW.inst sʷ) u′⊑) =
  view (all-imprecision-view C⊑C′)
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
world-coherent-quotient-representative-inst-path-identity-catchup-proofᵀ
    view {C⊑C′ = C⊑C′}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down
    widening@(quotient-cast-widening mode seal★
      (C.cast-inst hB occ s⊢ , NW.inst sʷ)
      mode′ seal★′ u′⊑) =
  view (all-imprecision-view C⊑C′)
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
