module proof.DGG.Catchup.StructuralInstantiationDescentDef where

-- File Charter:
--   * Records target-spine descent with a structural world-extension trace.
--   * Retains insertion history until source wrappers have been rebuilt.

open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Types using (Ty; TyCtx; TyVar; ＇_; `∀; _[_]ᵗ)
open import CastTerms using (Term; Value)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import Imprecision using (X⊑★)
open import Reduction using (StoreChanges; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef
open import proof.DGG.Catchup.StructuralSpineTypingDef
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (FuelStepSurface; Catchup⁻Embedᵀ; inst-alloc-decreaseᵀ)
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)


record StructuralInstantiationDescentPackage {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (γ : CTI2.CtxImp W)
    (M : Term Δᴸ) (V : Term Δᴿ) {A : Ty Δᴸ} {B E : Ty Δᴿ}
    (spine : InstantiationSpine B E)
    (q : A CTI2.⊑ᵂ⟨ W ⟩ E) : Set₁ where
  field
    target-descent : StructuralTargetInstantiationPackage W V spine
    final-relation :
      StructuralTargetInstantiationPackage.W′ target-descent CTI2.∣
        ECR.mapCtxᴿ (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext
            target-descent)) γ
        ⊢² M ⊑
          StructuralTargetInstantiationPackage.final target-descent ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext
                target-descent)) q


record StructuralNamePostPlan {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (A : Ty Δᴸ) (E : Ty Δᴿ)
    (q : A CTI2.⊑ᵂ⟨ W ⟩ E) : Set₁ where
  inductive
  field
    cast-child : ∀ {A₀ : Ty Δᴸ} {ν : Env∼ Δᴸ}
      → ν ⊢ A₀ ∼ A
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ W ⟩ E ]
          StructuralNamePostPlan W A₀ E q₀

    plain-Λ-child : ∀ {A₀ : Ty (suc Δᴸ)}
      → A ≡ `∀ A₀
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ E ]
          StructuralNamePostPlan
            (CTI2.liftWorldLeft X⊑★ W) A₀ E q₀

    smart-Λ-child : ∀ {Δᵐ} {A₀ : Ty (suc Δᴸ)}
        {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
      → A ≡ `∀ A₀
      → CTI2.SmartCommaLiftᴸ W Wᵐ
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ Wᵐ ⟩ E ]
          StructuralNamePostPlan Wᵐ A₀ E q₀

    reveal-child : ∀ {A₀ : Ty Δᴸ} {Wᵖ Xᴸ?}
        {c : Conv↑ Δᴸ A₀ A}
      → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ Wᵖ ⟩ E ]
          StructuralNamePostPlan Wᵖ A₀ E q₀

    conceal-child : ∀ {A₀ : Ty Δᴸ} {Wᵖ Xᴸ? Xᴿ?}
        {c : Conv↓ Δᴸ A₀ A}
      → CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ Wᵖ ⟩ E ]
          StructuralNamePostPlan Wᵖ A₀ E q₀


record StructuralNameChainPlan {fuel : ℕ} {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (γ : CTI2.CtxImp W)
    (A : Ty Δᴸ) (E : Ty Δᴿ)
    (q : A CTI2.⊑ᵂ⟨ W ⟩ E)
    (plan : StructuralNamePostPlan W A E q) : Set₁ where
  inductive
  field
    cast-child : ∀ {A₀ : Ty Δᴸ} {ν : Env∼ Δᴸ}
        {B : Ty Δᴿ} {spine : InstantiationSpine B E}
      → (c : ν ⊢ A₀ ∼ A)
      → TargetFrameAbsorptionChain W γ A spine q
      → SpineTypedʷ {fuel = fuel} W spine
      → let child = StructuralNamePostPlan.cast-child plan c in
          Σ[ child-chain ∈
            TargetFrameAbsorptionChain W γ A₀ spine (proj₁ child) ]
          Σ[ child-typed ∈ SpineTypedʷ {fuel = fuel} W spine ]
            StructuralNameChainPlan {fuel = fuel} W γ A₀ E (proj₁ child)
              (proj₂ child)

    plain-Λ-child : ∀ {A₀ : Ty (suc Δᴸ)}
        {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft X⊑★ W)}
        {B : Ty Δᴿ} {spine : InstantiationSpine B E}
      → (eq : A ≡ `∀ A₀)
      → CTI2.LiftCtxᴸ X⊑★ γ γᴸ
      → TargetFrameAbsorptionChain W γ A spine q
      → SpineTypedʷ {fuel = fuel} W spine
      → let child = StructuralNamePostPlan.plain-Λ-child plan eq in
          Σ[ child-chain ∈
            TargetFrameAbsorptionChain
              (CTI2.liftWorldLeft X⊑★ W) γᴸ A₀ spine
              (proj₁ child) ]
          Σ[ child-typed ∈
            SpineTypedʷ {fuel = fuel}
              (CTI2.liftWorldLeft X⊑★ W) spine ]
            StructuralNameChainPlan {fuel = fuel}
              (CTI2.liftWorldLeft X⊑★ W)
              γᴸ A₀ E (proj₁ child) (proj₂ child)

    smart-Λ-child : ∀ {Δᵐ} {A₀ : Ty (suc Δᴸ)}
        {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
        {γᵐ : CTI2.CtxImp Wᵐ}
        {B : Ty Δᴿ} {spine : InstantiationSpine B E}
      → (eq : A ≡ `∀ A₀)
      → (liftW : CTI2.SmartCommaLiftᴸ W Wᵐ)
      → CTI2.SmartLiftCtxᴸ γ γᵐ
      → TargetFrameAbsorptionChain W γ A spine q
      → SpineTypedʷ {fuel = fuel} W spine
      → let child = StructuralNamePostPlan.smart-Λ-child plan eq liftW in
          Σ[ child-chain ∈
            TargetFrameAbsorptionChain Wᵐ γᵐ A₀ spine
              (proj₁ child) ]
          Σ[ child-typed ∈ SpineTypedʷ {fuel = fuel} Wᵐ spine ]
            StructuralNameChainPlan {fuel = fuel} Wᵐ γᵐ A₀ E
              (proj₁ child)
              (proj₂ child)

    reveal-child : ∀ {A₀ : Ty Δᴸ} {Wᵖ Xᴸ?}
        {γᵖ : CTI2.CtxImp Wᵖ} {c : Conv↑ Δᴸ A₀ A}
        {B : Ty Δᴿ} {spine : InstantiationSpine B E}
      → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
      → CTI2.SameCtx γ γᵖ
      → TargetFrameAbsorptionChain W γ A spine q
      → SpineTypedʷ {fuel = fuel} W spine
      → let child = StructuralNamePostPlan.reveal-child plan {c = c} rb in
          Σ[ child-chain ∈
            TargetFrameAbsorptionChain Wᵖ γᵖ A₀ spine
              (proj₁ child) ]
          Σ[ child-typed ∈ SpineTypedʷ {fuel = fuel} Wᵖ spine ]
            StructuralNameChainPlan {fuel = fuel} Wᵖ γᵖ A₀ E
              (proj₁ child)
              (proj₂ child)

    conceal-child : ∀ {A₀ : Ty Δᴸ} {Wᵖ Xᴸ? Xᴿ?}
        {γᵖ : CTI2.CtxImp Wᵖ} {c : Conv↓ Δᴸ A₀ A}
        {B : Ty Δᴿ} {spine : InstantiationSpine B E}
      → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
      → CTI2.SameCtx γ γᵖ
      → TargetFrameAbsorptionChain W γ A spine q
      → SpineTypedʷ {fuel = fuel} W spine
      → let child = StructuralNamePostPlan.conceal-child plan {c = c} rb in
          Σ[ child-chain ∈
            TargetFrameAbsorptionChain Wᵖ γᵖ A₀ spine
              (proj₁ child) ]
          Σ[ child-typed ∈ SpineTypedʷ {fuel = fuel} Wᵖ spine ]
            StructuralNameChainPlan {fuel = fuel} Wᵖ γᵖ A₀ E
              (proj₁ child)
              (proj₂ child)


StructuralNameInstantiationᵀ : Set₁
StructuralNameInstantiationᵀ =
  ∀ {fuel Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
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
  → StructuralTargetInstantiationPackage.W′ target CTI2.∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        γ
      ⊢² M ⊑ StructuralTargetInstantiationPackage.final target ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          q
