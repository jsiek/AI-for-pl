module proof.DGG.Catchup.StructuralStrictViewSurfaceDef where

-- File Charter:
--   * States the NS-4 view-dispatched strict target-head surfaces.
--   * Each surface consumes the source/target derivation core, the peeled
--     child target package, and the caller's plan/chain state.
--   * Each surface returns exactly the child endpoint, post-plan, relation,
--     and target-frame absorption chain needed by the structural worker.

import Data.Fin as Fin
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

open import Types using
  (Ty; TyCtx; TyVar; NonVar; _∈ᵗ_; ★; ＇_; `∀; _[_]ᵗ; ⇑ᵗ)
open import Consistency using
  (Env∼; _↪ᵗ_; wk↪ᵗ; extᵐ; genᵐ; _⊢_∼_; ∀ᶜ_; gen_; _[_]ᶜ)
open import Conversion using (Conv↑; Conv↓; `∀↑_; `∀↓_; 〖_,_↑_〗)
open import CastTerms using
  (Term; Value; GenSafe; Λ_; _⟨_⟩; _↑_; _↓_; _⦂∀_[_]; ⇑ᵗᵐ)
open import Reduction using
  (keep; bind; applyTy; applyBody; applyStores; _∷_; [])
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef
open import proof.DGG.Catchup.StructuralSpineTypingDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (FuelStepSurface; ResidualCastBuilderᵀ; inst-alloc-decreaseᵀ)
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)


StructuralNameConcealEqualSourceOKᵀ : Set₁
StructuralNameConcealEqualSourceOKᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {U : Term Δᴸ} {V : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ} {Xᴸ? Xᴿ?}
    {c : Conv↓ Δᴸ A A′}
  → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → CTI2.SourceConcealOK Wᵖ U c Xᴿ? V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → let child = structural-tag-rebase-atᴸ
          (StructuralTargetInstantiationPackage.structural-ext target) rb
     in CTI2.SourceConcealOK
          (StructuralTagRebaseAtᴸResult.Wᵖ′ child) U c
          (mapPivotChanges
            (StructuralTargetInstantiationPackage.χs target) Xᴿ?)
          (StructuralTargetInstantiationPackage.final target)


StructuralNameConcealEqualNoTargetᵀ : Set₁
StructuralNameConcealEqualNoTargetᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {V : Term Δᴿ}
    {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {Xᴸ : TyVar Δᴸ}
  → (rb : CTI2.TagRebaseAtᴸ Wᵖ W (just Xᴸ) nothing)
  → CTI2.NoTargetOccupantAtSource Wᵖ Xᴸ
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → let child = structural-tag-rebase-atᴸ
          (StructuralTargetInstantiationPackage.structural-ext target) rb
     in CTI2.NoTargetOccupantAtSource
          (StructuralTagRebaseAtᴸResult.Wᵖ′ child) Xᴸ


record StructuralStrictChild {fuel : ℕ} {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
    (γ : CTI2.CtxImp W)
    (M : Term Δᴸ)
    (V : Term Δᴿ)
    (A : Ty Δᴸ)
    (B E : Ty Δᴿ)
    (spine : InstantiationSpine B E)
    (q : A CTI2.⊑ᵂ⟨ W ⟩ E) : Set₁ where
  field
    child-endpoint : A CTI2.⊑ᵂ⟨ W ⟩ B
    child-value : Value V
    child-plan : StructuralNamePostPlan W A E q
    child-chain-plan :
      StructuralNameChainPlan {fuel = fuel} W γ A E q child-plan
    child-relation : W CTIR.∣ γ ⊢² M ⊑ V ∶ child-endpoint
    child-chain : TargetFrameAbsorptionChain W γ A spine q
    child-typed : SpineTypedʷ {fuel = fuel} W spine


StructuralΛStrictSurfaceᵀ : Set₁
StructuralΛStrictSurfaceᵀ =
  ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {π : Δ ↪ᵗ Δ₁}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → W CTIR.∣ γ ⊢² M ⊑ Λ V ∶ p
  → Value M
  → Value V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ A
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTI2.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTI2.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁
      (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
      (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine))
  → let ext₁ = target-insert-bind-world-extendᴿ ins follows
     in StructuralStrictChild {fuel = fuel} W₁ (ECR.mapCtxᴿ ext₁ γ) M
          (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
          A _ (applyTy (bind (＇ X)) E)
          (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
            mapInstantiationSpine (bind (＇ X)) spine)
          (ECR.transport⊑ᵂ ext₁ q)


StructuralAllCastStrictSurfaceᵀ : Set₁
StructuralAllCastStrictSurfaceᵀ =
  ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {μ : Env∼ Δᴿ}
    {d : extᵐ μ ⊢ B ∼ C}
    {p : Aₛ CTI2.⊑ᵂ⟨ W ⟩ `∀ C}
    {q : Aₛ CTI2.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W Aₛ E q)
  → StructuralNameChainPlan {fuel = fuel} W γ Aₛ E q plan
  → W CTIR.∣ γ ⊢² M ⊑ V ⟨ ∀ᶜ d ⟩ ∶ p
  → Value M
  → Value V
  → (spine : InstantiationSpine (C [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame C X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame C X refl refl ▻ⁱ spine)
  → (child-target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine))
  → StructuralStrictChild {fuel = fuel} W γ M V Aₛ (`∀ B) E
      (name-type-app-frame B X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine)
      q


StructuralGenStrictSurfaceᵀ : Set₁
StructuralGenStrictSurfaceᵀ =
  ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {Aₛ : Ty Δᴸ} {A : Ty Δᴿ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ} {μ : Env∼ Δᴿ}
    {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    {π : Δ ↪ᵗ Δ₁}
    {p : Aₛ CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : Aₛ CTI2.⊑ᵂ⟨ W ⟩ E}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
  → (plan : StructuralNamePostPlan W Aₛ E q)
  → StructuralNameChainPlan {fuel = fuel} W γ Aₛ E q plan
  → (A≢★ : A ≢ ★)
  → W CTIR.∣ γ ⊢² M ⊑ V ⟨ (gen c) A≢★ ⟩ ∶ p
  → Value M
  → Value V
  → GenSafe c
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTI2.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTI2.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁ (⇑ᵗᵐ V)
      (cast-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine))
  → let ext₁ = target-insert-bind-world-extendᴿ ins follows
     in StructuralStrictChild {fuel = fuel} W₁ (ECR.mapCtxᴿ ext₁ γ) M
          (⇑ᵗᵐ V) Aₛ _ (applyTy (bind (＇ X)) E)
          (cast-frame c ▻ⁱ
            reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
            type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
            mapInstantiationSpine (bind (＇ X)) spine)
          (ECR.transport⊑ᵂ ext₁ q)


StructuralRevealStrictSurfaceᵀ : Set₁
StructuralRevealStrictSurfaceᵀ =
  ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {c : Conv↑ (suc Δᴿ) C B}
    {π : Δ ↪ᵗ Δ₁}
    {p : Aₛ CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : Aₛ CTI2.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W Aₛ E q)
  → StructuralNameChainPlan {fuel = fuel} W γ Aₛ E q plan
  → W CTIR.∣ γ ⊢² M ⊑ V ↑ `∀↑ c ∶ p
  → Value M
  → Value V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTI2.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTI2.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁ (⇑ᵗᵐ V)
      (name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
          refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        reveal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine))
  → let ext₁ = target-insert-bind-world-extendᴿ ins follows
     in StructuralStrictChild {fuel = fuel} W₁ (ECR.mapCtxᴿ ext₁ γ) M
          (⇑ᵗᵐ V) Aₛ _ (applyTy (bind (＇ X)) E)
          (name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
              refl refl ▻ⁱ
            type-transport-frame (applyBody-open-zero C) ▻ⁱ
            reveal-frame c ▻ⁱ
            reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
            type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
            mapInstantiationSpine (bind (＇ X)) spine)
          (ECR.transport⊑ᵂ ext₁ q)


StructuralConcealStrictSurfaceᵀ : Set₁
StructuralConcealStrictSurfaceᵀ =
  ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {c : Conv↓ (suc Δᴿ) C B}
    {π : Δ ↪ᵗ Δ₁}
    {p : Aₛ CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : Aₛ CTI2.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W Aₛ E q)
  → StructuralNameChainPlan {fuel = fuel} W γ Aₛ E q plan
  → W CTIR.∣ γ ⊢² M ⊑ V ↓ `∀↓ c ∶ p
  → Value M
  → Value V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTI2.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTI2.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁ (⇑ᵗᵐ V)
      (name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
          refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        conceal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine))
  → let ext₁ = target-insert-bind-world-extendᴿ ins follows
     in StructuralStrictChild {fuel = fuel} W₁ (ECR.mapCtxᴿ ext₁ γ) M
          (⇑ᵗᵐ V) Aₛ _ (applyTy (bind (＇ X)) E)
          (name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
              refl refl ▻ⁱ
            type-transport-frame (applyBody-open-zero C) ▻ⁱ
            conceal-frame c ▻ⁱ
            reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
            type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
            mapInstantiationSpine (bind (＇ X)) spine)
          (ECR.transport⊑ᵂ ext₁ q)


record StructuralStrictViewSurfaces : Set₁ where
  field
    conceal-equal-source-ok : StructuralNameConcealEqualSourceOKᵀ
    conceal-equal-no-target : StructuralNameConcealEqualNoTargetᵀ
    Λ-cell : StructuralΛStrictSurfaceᵀ
    ∀-cast-cell : StructuralAllCastStrictSurfaceᵀ
    gen-cell : StructuralGenStrictSurfaceᵀ
    reveal-cell : StructuralRevealStrictSurfaceᵀ
    conceal-cell : StructuralConcealStrictSurfaceᵀ


StructuralNameInstantiationᵀ : Set₁
StructuralNameInstantiationᵀ =
  StructuralStrictViewSurfaces
  → ∀ {fuel Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → FuelStepSurface fuel
  → ResidualCastBuilderᵀ
  → inst-alloc-decreaseᵀ
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → W CTIR.∣ γ ⊢² M ⊑ V ∶ p
  → Value M
  → Value V
  → AllValueView V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ A
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → (target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → StructuralTargetInstantiationPackage.W′ target CTIR.∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        γ
      ⊢² M ⊑ StructuralTargetInstantiationPackage.final target ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          q
