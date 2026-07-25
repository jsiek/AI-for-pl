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
open import Agda.Builtin.Equality using (refl)
open import CastImprecisionShape using (shape-inst)
open import Data.Product using (_,_)
open import ImprecisionWf using (ν)
open import ImprecisionComposition using
  (quotient-boundary-square)
import NarrowWiden as NW
open import NuReduction using (β-inst; pure-step)
open import NuTermImprecision using
  (left-id-only-compatible; seal★-tag-or-id)
open import NuTerms using (no•-⟨⟩; _⟨_⟩)
import QuotientedTermImprecision as QTI
open import Relation.Binary.PropositionalEquality using (sym)
open QTI using (quotient-cast-widening; quotient-id-widening)
open import TermTyping using (cast-tag-or-id)
open import proof.Core.Properties.CastImprecision using
  ( compose-cast-left
  ; instSafe-source-admissible
  ; seal★-inst-shift
  ; ⊑-transˡ-castᵢ
  )
open import proof.Core.Properties.CoercionProperties using (ModeIncl-inst)
open import proof.Core.Properties.NuCastImprecision using
  (nu-narrowing⇒⊑ᵢ; nu-widening⇒⊑ᵢ)
open import
  proof.Core.Properties.ImprecisionCompositionProperties
  using (compose-result-unique)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( compose-source-ν-body
  ; imprecision-composition-shape-transport
  ; nu-narrowing⇒⊑ᵢ-shape
  ; nu-widening⇒⊑ᵢ-shape
  ; shape-⊑-trans-compose
  )
open import
  proof.Quotient.NuImprecisionQuotientInstPathProperties
  using
  (normalized-path-refl-source-permutation-shape-equal)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef
  using (WorldCoherentFinalSourceNuCastCatchupᵀ)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastIndexBodyViewDef
  using (source-only-index-body)
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
    final cast-widen {E≈E = E≈E} {{safe = safe}}
    {pC = pC} {T≈T = T≈T} {pA = pA}
    occ r source-normal target-normal
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    d⊒ d-shape d′⊒ d′-shape
    (quotient-boundary-square
      source-shape left-comp target-shape right-comp)
    V⊑V′
    (quotient-id-widening
      (C.cast-inst hB occ′ s⊢ , NW.inst sʷ) u′⊑)
    (shape-inst s-shape) u′-shape
    (quotient-boundary-square
      up-source-shape up-left up-target-shape up-right)
    =
  world-coherent-left-catchup-prepend-keep-step
    (pure-step (β-inst vVd))
    (final coherent exclusive wfL cast-tag-or-id
      (seal★-inst-shift seal★-tag-or-id) s⊑
      (source-only-index-body
        {{safe = instSafe-source-admissible s⊢ sʷ}}
        {occ = occ′} _)
      s-shape body-comp
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

  source-shape-eq =
    normalized-path-refl-source-permutation-shape-equal
      source-normal source-shape

  target-shape-eq =
    normalized-path-refl-source-permutation-shape-equal
      target-normal target-shape

  left-comp′ =
    imprecision-composition-shape-transport
      source-shape-eq refl refl left-comp

  q-down-canonical =
    shape-⊑-trans-compose
      (compose-cast-left left-id-only-compatible)
      (nu-narrowing⇒⊑ᵢ wfL (λ α ()) d⊒) pC

  q-down-comp =
    imprecision-composition-shape-transport
      (sym (nu-narrowing⇒⊑ᵢ-shape
        wfL (λ α ()) d⊒ d-shape))
      refl refl q-down-canonical

  left-result-eq =
    compose-result-unique left-comp′ q-down-comp

  right-q-down-comp =
    imprecision-composition-shape-transport
      refl (sym target-shape-eq) (sym left-result-eq)
      right-comp

  up-source-shape-eq =
    normalized-path-refl-source-permutation-shape-equal
      source-normal up-source-shape

  up-target-shape-eq =
    normalized-path-refl-source-permutation-shape-equal
      target-normal up-target-shape

  up-left′ =
    imprecision-composition-shape-transport
      up-source-shape-eq refl refl up-left

  q-up-canonical =
    shape-⊑-trans-compose
      (compose-cast-left left-id-only-compatible)
      (nu-widening⇒⊑ᵢ wfL (λ α ()) u⊑) pA

  q-up-comp =
    imprecision-composition-shape-transport
      (sym (nu-widening⇒⊑ᵢ-shape
        wfL (λ α ()) u⊑ (shape-inst s-shape)))
      refl refl q-up-canonical

  up-result-eq =
    compose-result-unique up-left′ q-up-comp

  exact-q-up-comp =
    imprecision-composition-shape-transport
      refl refl (sym up-result-eq) up-left′

  body-comp = compose-source-ν-body exact-q-up-comp

  right-q-up-comp =
    imprecision-composition-shape-transport
      refl (sym up-target-shape-eq) (sym up-result-eq)
      up-right

  d-rel =
    QTI.⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
      (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ d′⊒)
      (QTI.cast⊒⊑ᵀ cast-tag-or-id seal★-tag-or-id
        (NW.narrow-mode-relax C.id-only≤tag-or-idᵈ d⊒)
        V⊑V′ q-down d-shape q-down-comp)
      (ν safe occ r) d′-shape right-q-down-comp

  L⊑V′u′ = QTI.⊑cast⊑idᵀ (λ α ()) u′⊑ d-rel q
    u′-shape right-q-up-comp

  s⊑ =
    NW.widen-mode-relax
      (ModeIncl-inst C.id-only≤tag-or-idᵈ)
      (s⊢ , NW.instSafe→widening sʷ)
world-coherent-quotient-representative-inst-path-identity-source-id-down-catchup-proofᵀ
    final cast-widen {{safe = safe}} occ r
    source-normal target-normal
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    d⊒ d-shape d′⊒ d′-shape down-square V⊑V′
    (quotient-cast-widening mode seal★ u⊑ mode′ seal★′ u′⊑)
    u-shape u′-shape up-square =
  cast-widen {{safe}} occ r coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′
    d⊒ d-shape d′⊒ d′-shape down-square V⊑V′
    mode seal★ u⊑ mode′ seal★′ u′⊑
    u-shape u′-shape up-square
