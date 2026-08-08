module proof.DGG.Inversion.SourceStripProof where

-- File Charter:
--   * Provides the source-strip inhabitants consumed by the composed target
--     tag/seal walk.
--   * Keeps the structural strip proof behind the `SourceStripDef` surface.
--   * Exposes no right-injection theorem directly.

open import Relation.Binary.PropositionalEquality using (refl)
  renaming (subst to subst≡)
open import Data.Product using (_,_)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term)
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip; SourceTagSealCore;
   SourceCorePremise; core-sealed; core-terminus; core-tagged;
   core-untagged)
open import proof.DGG.Inversion.TargetStripDef using
  (TargetStripAt★Data; target-strip★-data)
open import proof.DGG.Inversion.TargetStripLemma using
  (target-strip-at★)
open import proof.DGG.Inversion.SourceStripWorkerProof using
  (source-column-strip-worker; source-spine-strip-worker)

private
  rebase-target-membership-forward : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : CTI2.World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
    → CTI2.RebaseAt W′ W X Y
    → CTI2.targetStoreʷ W ∋ Y ⦂ S
    → CTI2.targetStoreʷ W′ ∋ Y ⦂ S
  rebase-target-membership-forward rb Y∈ =
    subst≡ (λ Σ → Σ ∋ _ ⦂ _)
      (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb)) Y∈

source-column-strip : SourceColumnStrip
source-column-strip = source-column-strip-worker

source-spine-strip : SourceSpineStrip
source-spine-strip = source-spine-strip-worker

source-tag-seal-core : SourceTagSealCore
source-tag-seal-core sv vU mono rb sc source∈ target∈
    (core-untagged qᶜ D) =
  core-sealed
    (_ , _ , qᶜ , mono , sc , CTI2.rebase-varᴸ rb ,
      rebase-target-membership-forward rb target∈ , D)
source-tag-seal-core {Wᵖ = Wᵖ} {γᵖ = γᵖ} {Xᴸ = Xᴸ}
    {ν = ν} {cY = cY} {p = p} sv vU mono rb sc source∈
    target∈
    (core-tagged D)
    with target-strip-at★ sv vU mono rb sc source∈ target∈ D
source-tag-seal-core {Wᵖ = Wᵖ} {γᵖ = γᵖ} {Xᴸ = Xᴸ}
    {ν = ν} {cY = cY} {p = p} sv vU mono rb sc source∈
    target∈ (core-tagged D)
    | target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
        target∈★ q★ premise★ reemit =
  core-terminus
    (U★ , Y★ , _ , refl , W★ , γ★ , mono★ , same★ ,
      boundary★ , target∈★ , q★ , premise★ , reemit)
