module proof.DGG.Catchup.StructuralInstantiationDescentProof where

-- File Charter:
--   * Builds the zero-spine structural descent package.
--   * Erases structural traces to the public instantiation package.

open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
  renaming (subst to subst≡)

open import Types using (Ty; TyVar; ＇_; `∀; _[_]ᵗ)
open import CastTerms using (Term; Value)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores;
   applyTy; _—→[_]_; ↠-refl)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.InstInversionDef using
  (InstSpineDescentPackage)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof
open import proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef
open import proof.DGG.Catchup.StructuralSpineTypingDef
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (FuelStepSurface; Catchup⁻Embedᵀ; inst-alloc-decreaseᵀ)
open import proof.DGG.Catchup.ColumnSupportProof using (mapCtxᴿ-compose)
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)


structural-descent-zero : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → Value V
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ q
  → StructuralInstantiationDescentPackage W γ M V []ⁱ q
structural-descent-zero {W = W} {γ = γ} vV rel = record
  { target-descent = structural-target-zero vV
  ; final-relation = subst≡
      (λ γ′ → W CTI2.∣ γ′ ⊢² _ ⊑ _ ∶ _)
      (sym (ECR.mapCtxᴿ-same γ)) rel
  }


structural-descent-frame : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B C E : Ty Δᴿ}
    {frame : InstantiationFrame B C}
    {spine : InstantiationSpine C E}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → StructuralInstantiationDescentPackage W γ M
      (applyInstantiationFrame V frame) spine q
  → StructuralInstantiationDescentPackage W γ M V
      (frame ▻ⁱ spine) q
structural-descent-frame child = record
  { target-descent = structural-target-frame child-target
  ; final-relation =
      StructuralInstantiationDescentPackage.final-relation child
  }
  where
  child-target =
    StructuralInstantiationDescentPackage.target-descent child


structural-descent-keep-step : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V V₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B E B₁ : Ty Δᴿ}
    {spine : InstantiationSpine B E}
    {spine₁ : InstantiationSpine B₁ E}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → applyInstantiationSpine V spine —→[ keep ]
      applyInstantiationSpine V₁ spine₁
  → StructuralInstantiationDescentPackage W γ M V₁ spine₁ q
  → StructuralInstantiationDescentPackage W γ M V spine q
structural-descent-keep-step {γ = γ} step child = record
  { target-descent = target
  ; final-relation = subst≡
      (λ γ′ → _ CTI2.∣ γ′ ⊢² _ ⊑ _ ∶ _)
      (sym (mapCtxᴿ-structural-keep child-plan γ))
      (StructuralInstantiationDescentPackage.final-relation child)
  }
  where
  child-target =
    StructuralInstantiationDescentPackage.target-descent child
  child-plan =
    StructuralTargetInstantiationPackage.structural-ext child-target
  target = structural-target-keep-step step child-target


structural-descent-bind-step : ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ} {V₁ : Term (suc Δᴿ)}
    {A : Ty Δᴸ} {R B E : Ty Δᴿ}
    {B₁ : Ty (suc Δᴿ)} {π : Δ ↪ᵗ Δ₁}
    {spine : InstantiationSpine B E}
    {spine₁ : InstantiationSpine B₁ (applyTy (bind R) E)}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTI2.targetStoreʷ W₁ ≡
      applyStores (bind R ∷ []) (CTI2.targetStoreʷ W))
  → applyInstantiationSpine V spine —→[ bind R ]
      applyInstantiationSpine V₁ spine₁
  → let ext₁ = target-insert-bind-world-extendᴿ ins follows
     in StructuralInstantiationDescentPackage W₁
          (ECR.mapCtxᴿ ext₁ γ) M V₁ spine₁
          (ECR.transport⊑ᵂ ext₁ q)
  → StructuralInstantiationDescentPackage W γ M V spine q
structural-descent-bind-step {γ = γ} ins follows step child = record
  { target-descent = target
  ; final-relation = subst≡
      (λ γ′ → _ CTI2.∣ γ′ ⊢² _ ⊑ _ ∶ _)
      (mapCtxᴿ-compose ext₁ child-ext γ)
      (StructuralInstantiationDescentPackage.final-relation child)
  }
  where
  ext₁ = target-insert-bind-world-extendᴿ ins follows
  child-target =
    StructuralInstantiationDescentPackage.target-descent child
  child-ext = structural-world-extendᴿ
    (StructuralTargetInstantiationPackage.structural-ext child-target)
  target = structural-target-bind-step ins follows step child-target


erase-structural-descent : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ} {A : Ty Δᴸ} {B E : Ty Δᴿ}
    {spine : InstantiationSpine B E}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → StructuralInstantiationDescentPackage W γ M V spine q
  → InstSpineDescentPackage W γ M
      (applyInstantiationSpine V spine) q
erase-structural-descent pkg = record
  { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ target
  ; χs = StructuralTargetInstantiationPackage.χs target
  ; Δ′ = StructuralTargetInstantiationPackage.Δ′ target
  ; W′ = StructuralTargetInstantiationPackage.W′ target
  ; ext = structural-world-extendᴿ
      (StructuralTargetInstantiationPackage.structural-ext target)
  ; final = StructuralTargetInstantiationPackage.final target
  ; final-value = StructuralTargetInstantiationPackage.final-value target
  ; post-reduction = StructuralTargetInstantiationPackage.post-reduction target
  ; final-relation =
      StructuralInstantiationDescentPackage.final-relation pkg
  }
  where
  target = StructuralInstantiationDescentPackage.target-descent pkg


structural-name-package :
  StructuralNameInstantiationᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W}
      {M : Term Δᴸ} {V : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → Catchup⁻Embedᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W A E q)
    → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
    → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
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
    → StructuralInstantiationDescentPackage W γ M V
        (name-type-app-frame B X refl refl ▻ⁱ spine) q
structural-name-package worker fuel-step catchup⁻-embed inst-decrease
    plan chain-plan rel vM vV view spine chain typed target =
  record
    { target-descent = target
    ; final-relation =
        worker fuel-step catchup⁻-embed inst-decrease plan chain-plan
          rel vM vV view spine chain typed target
    }


erase-structural-name-root :
  StructuralNameInstantiationᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W}
      {M : Term Δᴸ} {V : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → Catchup⁻Embedᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W A E q)
    → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
    → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
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
    → InstSpineDescentPackage W γ M
        (applyInstantiationSpine V
          (name-type-app-frame B X refl refl ▻ⁱ spine)) q
erase-structural-name-root worker fuel-step catchup⁻-embed inst-decrease
    plan chain-plan rel vM vV view spine chain typed target =
  erase-structural-descent
    (structural-name-package worker fuel-step catchup⁻-embed
      inst-decrease plan chain-plan rel vM vV view spine chain typed target)
