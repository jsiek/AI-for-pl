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
open import Conversion using (seal)
open import CastTerms using (Term; Value; _↓_; _⟨_⟩)
open import Imprecision
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.SealTransferCore as STC
open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip; SourceTagSealCore;
   SourceColumnStripWorker; SourceSpineStripWorker;
   SourceTagSealCoreBranch; SourceCorePremise; core-sealed;
   core-terminus; core-tagged; core-terminus-nonstar; core-untagged)
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open import proof.DGG.Inversion.TargetStripDef using
  (TargetStripAt★Data; target-strip★-data; target-strip★-paired)
open import proof.DGG.Inversion.TargetStripLemma using
  (target-strip-at★)
open CTI2 using
  (World;
   CtxImp;
   RebaseAt;
   _⊑ᵂ⟨_⟩_;
   sourceStoreʷ;
   targetStoreʷ)
open CTIR using (_∣_⊢²_⊑_∶_)

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

  source-tag-seal-core-tagged : ∀ {Δᴸ Δᴿ Δ}
      {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
      {P : Term Δᴸ} {U : Term Δᴿ}
      (A : Ty Δᴸ)
      {S : Ty Δᴿ} {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ ★}
      {q : (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y)}
    → SpineValue P
    → Value U
    → CTI2.ImpEnvMono Wᵒ Wᵖ
    → RebaseAt Wᵖ Wᵒ Xᴸ Y
    → CTI2.SameCtx γᵒ γᵖ
    → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
    → targetStoreʷ Wᵒ ∋ Y ⦂ S
    → Wᵖ ∣ γᵖ ⊢² P ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
    → SourceTagSealCoreBranch Wᵒ γᵒ P A U Xᴸ Y S cY Wᵖ γᵖ p
  source-tag-seal-core-tagged ★ sv vU mono rb sc source∈ target∈ D
      with target-strip-at★ sv vU mono rb sc source∈ target∈ D
  source-tag-seal-core-tagged ★ sv vU mono rb sc source∈ target∈ D
      | target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
          target∈★ q★ premise★ reemit =
    core-terminus refl
      (U★ , Y★ , _ , refl , W★ , γ★ , mono★ , same★ ,
        boundary★ , target∈★ , q★ , premise★ , reemit)
  source-tag-seal-core-tagged {Wᵒ = Wᵒ} {γᵒ = γᵒ}
      (＇ X) sv vU mono rb sc source∈ target∈ D
      with target-strip-at★ sv vU mono rb sc source∈ target∈ D
  source-tag-seal-core-tagged {Wᵒ = Wᵒ} {γᵒ = γᵒ}
      (＇ X) sv vU mono rb sc source∈ target∈ D
      | target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
          target∈★ q★ premise★ reemit =
    core-terminus-nonstar nonstar-X
      (U★ , Y★ , _ , refl , W★ , γ★ , mono★ , same★ ,
        boundary★ , target∈★ , q★ , premise★ , reemit)
  source-tag-seal-core-tagged {Wᵒ = Wᵒ} {γᵒ = γᵒ}
      (＇ X) sv vU mono rb sc source∈ target∈ D
      | target-strip★-paired {qᵒ = qᵒ} source∈ᵒ target∈ᵒ
          boundaryᵒ residualᵒ monoᵐ sameᵐ partnerᵐ premiseᵐ reemit =
    core-sealed
      (_ , _ , qᵒ ,
        STC.impEnvMono-refl {W = Wᵒ} ,
        STC.sameCtx-refl {γ = γᵒ} ,
        CTI2.rebase-varᴸ
          (CTI2.sameWorldRebaseAt
            (CTI2.RebaseAt.pivotAligned boundaryᵒ)
            (CTI2.RebaseAt.storeRepresentations boundaryᵒ)) ,
        target∈ᵒ ,
        residualᵒ)
  source-tag-seal-core-tagged (‵ ι) sv vU mono rb sc source∈
      target∈ D
      with target-strip-at★ sv vU mono rb sc source∈ target∈ D
  source-tag-seal-core-tagged (‵ ι) sv vU mono rb sc source∈
      target∈ D
      | target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
          target∈★ q★ premise★ reemit =
    core-terminus-nonstar nonstar-ι
      (U★ , Y★ , _ , refl , W★ , γ★ , mono★ , same★ ,
        boundary★ , target∈★ , q★ , premise★ , reemit)
  source-tag-seal-core-tagged (A ⇒ B) sv vU mono rb sc source∈
      target∈ D
      with target-strip-at★ sv vU mono rb sc source∈ target∈ D
  source-tag-seal-core-tagged (A ⇒ B) sv vU mono rb sc source∈
      target∈ D
      | target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
          target∈★ q★ premise★ reemit =
    core-terminus-nonstar nonstar-⇒
      (U★ , Y★ , _ , refl , W★ , γ★ , mono★ , same★ ,
        boundary★ , target∈★ , q★ , premise★ , reemit)
  source-tag-seal-core-tagged (`∀ A) sv vU mono rb sc source∈
      target∈ D
      with target-strip-at★ sv vU mono rb sc source∈ target∈ D
  source-tag-seal-core-tagged (`∀ A) sv vU mono rb sc source∈
      target∈ D
      | target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
          target∈★ q★ premise★ reemit =
    core-terminus-nonstar nonstar-∀
      (U★ , Y★ , _ , refl , W★ , γ★ , mono★ , same★ ,
        boundary★ , target∈★ , q★ , premise★ , reemit)

module SourceStripProofFrom
    (source-column-strip-worker : SourceColumnStripWorker)
    (source-spine-strip-worker : SourceSpineStripWorker)
  where

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
source-tag-seal-core {A = A} {p = p} {q = q} sv vU mono rb sc
    source∈ target∈
    (core-tagged D) =
  source-tag-seal-core-tagged A {p = p} {q = q} sv vU mono rb sc
    source∈ target∈ D
