{-# OPTIONS --safe #-}

module BodyStripCheck where

-- File Charter:
--   * Checks the lifted-Λ target-strip obligation without the retired
--     SourceStrip or TargetWalk surfaces.
--   * Reconstructs an ordinary target-strip result from the lifted body
--     result, including its target re-emission continuation.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  renaming (subst to subst≡)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using (seal)
open import CastTerms
open import Imprecision
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Inversion.TargetStripDef using
  (TargetStripAt★ᴸ; TargetStripAt★Data; TargetStripAt★ᴸData;
   target-strip★-data; target-strip★ᴸ-data; target-strip★ᴸ-paired)
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open import proof.TypeInTermSubst using (rename-occurs; toRename-keep-eq)

open CTX using
  (World;
   CtxImp;
   LiftCtxᴸ;
   RebaseAt;
   _⊑ᵂ⟨_⟩_;
   sourceStoreʷ;
   targetStoreʷ;
   tgtCtxʷ)
open CTI2 using (_∣_⊢²_⊑_∶_)

private
  all-to-star-obligation : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {A : Ty (suc Δᴸ)}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → A ⊑ᵂ⟨ CTX.liftWorldLeft W ⟩ ★
    → `∀ A ⊑ᵂ⟨ W ⟩ ★
  all-to-star-obligation {W = W} {A = A} Anv z∈A body★ =
    ∀⊑
      (renameNonVar (extᵗ (toRenameᵗ (CTX.ηᴸʷ W))) Anv)
      (rename-occurs (extᵗ (toRenameᵗ (CTX.ηᴸʷ W))) z∈A)
      (subst≡
        (λ T → instᵐ (CTX.impEnvʷ W) ⊢ T ⊑ ★)
        (renameᵗ-cong A (toRename-keep-eq (CTX.ηᴸʷ W)))
        body★)

  nonvar-var-⊥ : ∀ {Δ} {A : Ty Δ} {X : TyVar Δ}
    → A ≡ ＇ X
    → NonVar A
    → ⊥
  nonvar-var-⊥ refl ()

lambda-target-strip-from-lifted-data : ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
    {γᵇ : CtxImp (CTX.liftWorldLeft Wᵖ)}
    {V : Term (suc Δᴸ)} {U : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {bodyp : A ⊑ᵂ⟨ CTX.liftWorldLeft Wᵖ ⟩ ★}
    {q : `∀ A ⊑ᵂ⟨ Wᵖ ⟩ ★}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → Value V
  → ⟨ Δᴿ , targetStoreʷ Wᵖ , tgtCtxʷ γᵖ ⟩ ⊢
      (U ↓ seal Y S) ⟨ cY ⟩ ⦂ ★
  → CTX.liftWorldLeft Wᵖ ∣ γᵇ ⊢²
      V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ bodyp
  → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ Y S cY
      Wᵖ γᵖ γᵇ bodyp
  → TargetStripAt★Data Wᵒ γᵒ (Λ V) (`∀ A) U Xᴸ Y S cY
      Wᵖ γᵖ q
lambda-target-strip-from-lifted-data {γᵖ = γᵖ} {ν = ν}
    {cY = cY} {q = q} Anv z∈A liftγ vV target⊢ bodyD
    (target-strip★ᴸ-data U★ Y★ W★ γ★ γ★ᴸ lift★ mono★
      same★ boundary★ target∈★ body★ U⊢★ premise★ reemit) =
  target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
    target∈★ q★ premiseΛ (λ _ →
      CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ (reemit premise★) q)
  where
  q★ = all-to-star-obligation {W = W★} Anv z∈A body★
  premiseΛ = CTI2.Λ⊑² Anv z∈A lift★ vV U⊢★ premise★ q★
lambda-target-strip-from-lifted-data Anv z∈A liftγ vV target⊢ bodyD
    (target-strip★ᴸ-paired A≡ V≡ γᵒᴸ liftᵒ source∈ᵒ
      target∈ᵒ boundaryᵒ residualᵒ monoᵐ sameᵐ premiseᵐ reemit) =
  ⊥-elim (nonvar-var-⊥ A≡ Anv)

lambda-target-strip-from-member :
  TargetStripAt★ᴸ
  → ∀ {Δᴸ Δᴿ Δ}
      {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
      {γᵇ : CtxImp (CTX.liftWorldLeft Wᵖ)}
      {V : Term (suc Δᴸ)} {U : Term Δᴿ}
      {A : Ty (suc Δᴸ)} {S : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {bodyp : A ⊑ᵂ⟨ CTX.liftWorldLeft Wᵖ ⟩ ★}
      {q : `∀ A ⊑ᵂ⟨ Wᵖ ⟩ ★}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → SpineValue V
  → Value V
  → Value U
  → CTX.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTX.SameCtx γᵒ γᵖ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → ⟨ Δᴿ , targetStoreʷ Wᵖ , tgtCtxʷ γᵖ ⟩ ⊢
      (U ↓ seal Y S) ⟨ cY ⟩ ⦂ ★
  → CTX.liftWorldLeft Wᵖ ∣ γᵇ ⊢²
      V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ bodyp
  → TargetStripAt★Data Wᵒ γᵒ (Λ V) (`∀ A) U Xᴸ Y S cY
      Wᵖ γᵖ q
lambda-target-strip-from-member stripᴸ Anv z∈A liftγ sv vV vU mono rb
    sc source∈ target∈ target⊢ bodyD =
  lambda-target-strip-from-lifted-data Anv z∈A liftγ vV target⊢ bodyD
    (stripᴸ sv vU mono rb sc source∈ target∈ liftγ bodyD)
