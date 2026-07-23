module
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupProof
  where

-- File Charter:
--   * Proves the identity-widening half of non-vacuous source-only,
--     ordinary-down quotient-inst catch-up using sparse-store cast embedding.
--   * Passes `NonVar` and the occurrence proof into the exact inner
--     `ν` precision index; no vacuous source-only case is admitted.
--   * Delegates only the genuinely harder general-cast widening half.

import Coercions as C
open import Data.Product using (_,_)
open import ImprecisionWf using (ν)
import NarrowWiden as NW
open import NuReduction using (β-inst; pure-step)
open import NuTermImprecision using
  (left-id-only-compatible; seal★-tag-or-id)
open import NuTerms using (no•-⟨⟩; _⟨_⟩)
import QuotientedTermImprecision as QTI
open QTI using (quotient-cast-widening; quotient-id-widening)
open import TermTyping using (cast-tag-or-id)
open import proof.Core.Properties.CastImprecision using
  (seal★-inst-shift; ⊑-transˡ-castᵢ)
open import proof.Core.Properties.CoercionProperties using (ModeIncl-inst)
open import proof.Core.Properties.NuCastImprecision using
  (nu-narrowing⇒⊑ᵢ; nu-widening⇒⊑ᵢ)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef
  using (WorldCoherentFinalSourceNuCastCatchupᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftCatchupPrependKeepStep
  using (world-coherent-left-catchup-prepend-keep-step)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPathIdentity.Source.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupDef
  using
  (WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupᵀ)


world-coherent-quotient-representative-inst-path-identity-source-id-down-catchup-proofᵀ :
  WorldCoherentFinalSourceNuCastCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCastWidenCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathIdentitySourceIdDownCatchupᵀ
world-coherent-quotient-representative-inst-path-identity-source-id-down-catchup-proofᵀ
    final cast-widen {{safe = safe}} {pC = pC} {pA = pA}
    occ r coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d′⊒ V⊑V′
    (quotient-id-widening
      (C.cast-inst hB occ′ s⊢ , NW.inst sʷ) u′⊑) =
  world-coherent-left-catchup-prepend-keep-step
    (pure-step (β-inst vVd))
    (final coherent exclusive wfL cast-tag-or-id
      (seal★-inst-shift seal★-tag-or-id) s⊑
      vVd noVd (vV′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
      (no•-⟨⟩ (no•-⟨⟩ noV′)) L⊑V′u′)
  where
  u⊑ = C.cast-inst hB occ′ s⊢ , NW.inst sʷ

  q =
    ⊑-transˡ-castᵢ left-id-only-compatible
      (nu-widening⇒⊑ᵢ wfL (λ α ()) u⊑) pA

  q-down =
    ⊑-transˡ-castᵢ left-id-only-compatible
      (nu-narrowing⇒⊑ᵢ wfL (λ α ()) d⊒) pC

  d-rel =
    QTI.⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
      (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ d′⊒)
      (QTI.cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id
        (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ d⊒)
        V⊑V′ q-down)
      (ν safe occ r)

  L⊑V′u′ = QTI.⊑cast⊑idᵀ (λ α ()) u′⊑ d-rel q

  s⊑ =
    NW.widen-mode-relax
      (ModeIncl-inst C.id-only≤tag-or-idᵈ)
      (s⊢ , NW.instSafe→widening sʷ)
world-coherent-quotient-representative-inst-path-identity-source-id-down-catchup-proofᵀ
    final cast-widen {{safe = safe}} occ r
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d′⊒ V⊑V′
    (quotient-cast-widening mode seal★ u⊑ mode′ seal★′ u′⊑) =
  cast-widen {{safe}} occ r coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ d⊒ d′⊒ V⊑V′
    mode seal★ u⊑ mode′ seal★′ u′⊑
