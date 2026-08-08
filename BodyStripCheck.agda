module BodyStripCheck where

-- Scratch-only validation for the recut target-strip package.
-- Checks that the Λ core rebuild consumes the lifted strip result through
-- the reemit continuation rather than assuming the terminal target is the
-- original sealed target.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
  renaming (subst to subst≡)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using (seal)
open import CastTerms
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SourceStripDef using
  (SourceSpineStrip; SourceTagSealCore; SourceTagSealCoreBranch;
   core-terminus; core-tagged; spine-paired; spine-sealed;
   spine-tagged)
open import proof.DGG.Inversion.TargetStripDef using
  (TargetStripAt★; TargetStripAt★ᴸ; TargetStripAt★ᴸData)
open import proof.DGG.Inversion.TargetWalkDef using (TargetTagSealWalk)
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open import proof.TypeInTermSubst using (rename-occurs; toRename-keep-eq)

open CTI2 using
  (World; CtxImp; LiftCtxᴸ; RebaseAt; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; sourceStoreʷ; targetStoreʷ; tgtCtxʷ)

private
  all-to-star-obligation : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {A : Ty (suc Δᴸ)}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ ★
    → `∀ A ⊑ᵂ⟨ W ⟩ ★
  all-to-star-obligation {W = W} {A = A} Anv z∈A body★ =
    ∀⊑
      (renameNonVar (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) Anv)
      (rename-occurs (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) z∈A)
      (subst≡
        (λ T → instᵐ (CTI2.impEnvʷ W) ⊢ T ⊑ ★)
        (renameᵗ-cong A (toRename-keep-eq (CTI2.ηᴸʷ W)))
        body★)

------------------------------------------------------------------------
-- Validation A: the Λ core branch goes through reemit
------------------------------------------------------------------------

lambda-core-from-target-strip★ᴸ :
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
    {γᵇ : CtxImp (CTI2.liftWorldLeft X⊑★ Wᵖ)}
    {V : Term (suc Δᴸ)} {U : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ Wᵖ ⟩ ★}
    {q : `∀ A ⊑ᵂ⟨ Wᵖ ⟩ ★}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → Value V
  → ⟨ Δᴿ , targetStoreʷ Wᵖ , tgtCtxʷ γᵖ ⟩ ⊢
      (U ↓ seal Y S) ⟨ cY ⟩ ⦂ ★
  → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ Y S cY Wᵖ γᵖ γᵇ p
  → SourceTagSealCoreBranch Wᵒ γᵒ (Λ V) (`∀ A) U Xᴸ Y S
      cY Wᵖ γᵖ q
lambda-core-from-target-strip★ᴸ {Wᵖ = Wᵖ} {γᵖ = γᵖ}
    {ν = ν} {cY = cY} {q = q}
    Anv z∈A liftγ vV target⊢ d =
  core-terminus
    (U★ , Y★ , ★ , refl , W★ , γ★ , mono★ , same★ ,
      boundary★ , target∈★ , q★ ,
      CTI2.Λ⊑² Anv z∈A lift★ vV U⊢★ premise★ q★ ,
      λ _ → CTI2.Λ⊑² Anv z∈A liftγ vV target⊢
        (reemit premise★) q)
  where
  open TargetStripAt★ᴸData d
  q★ = all-to-star-obligation {W = W★} Anv z∈A body★

lambda-core-from-member :
  TargetStripAt★ᴸ
  → ∀ {Δᴸ Δᴿ Δ}
      {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
      {γᵇ : CtxImp (CTI2.liftWorldLeft X⊑★ Wᵖ)}
      {V : Term (suc Δᴸ)} {U : Term Δᴿ}
      {A : Ty (suc Δᴸ)} {S : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {bodyp : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ Wᵖ ⟩ ★}
      {q : `∀ A ⊑ᵂ⟨ Wᵖ ⟩ ★}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → SpineValue V
  → Value V
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → ⟨ Δᴿ , targetStoreʷ Wᵖ , tgtCtxʷ γᵖ ⟩ ⊢
      (U ↓ seal Y S) ⟨ cY ⟩ ⦂ ★
  → CTI2.liftWorldLeft X⊑★ Wᵖ ∣ γᵇ ⊢²
      V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ bodyp
  → SourceTagSealCoreBranch Wᵒ γᵒ (Λ V) (`∀ A) U Xᴸ Y S
      cY Wᵖ γᵖ q
lambda-core-from-member stripᴸ {q = q}
    Anv z∈A liftγ sv vV vU mono rb sc
    X∈★ Y∈ target⊢ bodyD =
  lambda-core-from-target-strip★ᴸ {q = q}
    Anv z∈A liftγ vV target⊢
    (stripᴸ sv vU mono rb sc X∈★ Y∈ liftγ bodyD)

------------------------------------------------------------------------
-- Validation B: walk-from-strip composition remains unchanged
------------------------------------------------------------------------

walk-from-strip-with-target-strip★ :
  SourceSpineStrip
  → TargetStripAt★
  → TargetStripAt★ᴸ
  → SourceTagSealCore
  → TargetTagSealWalk
walk-from-strip-with-target-strip★ strip strip★ strip★ᴸ core
    sv vU mono rb sc X∈ Y∈ D
    with strip sv vU mono rb sc X∈ Y∈ D
walk-from-strip-with-target-strip★ strip strip★ strip★ᴸ core
    sv vU mono rb sc X∈ Y∈ D
    | P , A , Xᵒ , Wᵒ , γᵒ , qᵒ , spine ,
        spine-sealed sealed final =
  final
walk-from-strip-with-target-strip★ strip strip★ strip★ᴸ core
    sv vU mono rb sc X∈ Y∈ D
    | P , A , Xᵒ , Wᵒ , γᵒ , qᵒ , spine ,
        spine-tagged Wᵖ γᵖ pᵖ monoᵒᵖ sameᵒᵖ boundaryᵖᵒ
          source∈ᵒ target∈ᵒ premiseᶜ finish =
  finish
    (core {Xᴸ = Xᵒ} {q = qᵒ}
      spine vU monoᵒᵖ boundaryᵖᵒ sameᵒᵖ source∈ᵒ target∈ᵒ
      (core-tagged premiseᶜ))
walk-from-strip-with-target-strip★ strip strip★ strip★ᴸ core
    sv vU mono rb sc X∈ Y∈ D
    | P , A , Xᵒ , Wᵒ , γᵒ , qᵒ , spine ,
        spine-paired paired final =
  final
