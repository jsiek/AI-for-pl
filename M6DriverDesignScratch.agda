module M6DriverDesignScratch where

-- File Charter:
--   * Root-level scratch for the M6 value-catch-up driver design.
--   * States the cast-column measure and the ValueCatchupRight² surface.
--   * Imports the M4/M5 Catchup modules read-only and checks that the
--     driver can refer to their worker surfaces without editing them.
--   * Uses a fuel-indexed design surface rather than implementing the final
--     well-founded recursion in this scratch pass.

import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; _↦_; ∀ᶜ_;
   _!; ？_; inst_; gen_; instᵐ; ↑ᶜ_; close-instᶜ)
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using
  (StoreChange; StoreChanges; _—↠[_]_; []; _∷_;
   applyTy; applyTys; applyConsistency; applyConsistencies)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.Catchup.ExtraCastRightProof as ECRP
import proof.DGG.Catchup.InstCatchupRightDef as ICRD
import proof.DGG.Catchup.InstCatchupRightProof as ICRP
open import proof.DGG.Inversion.RightInjInversion2Def
  using (RightInjInversion²)
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
import proof.DGG.ReachabilityCatalog as RC
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Cast-column measure
------------------------------------------------------------------------

-- This is structural size of the consistency proof carried by a target
-- cast, not just one unit per surface term cast.  The inst case is the
-- critical one: beta-inst removes the outer inst constructor but leaves a
-- renamed/closed body consistency as a surface cast.

castSize : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → μ ⊢ A ∼ B
  → ℕ
castSize (id a) = suc zero
castSize (c ↦ d) = suc (castSize c + castSize d)
castSize (∀ᶜ c) = suc (castSize c)
castSize (_! c) = suc (castSize c)
castSize (？ c) = suc (castSize c)
castSize (inst_ c B≢★) = suc (castSize c)
castSize (gen_ c A≢★) = suc (castSize c)
castSize Consistency.bot-elim = suc zero
castSize Consistency.bot-intro = suc zero

infixr 5 _▻ᶜ_

data CastColumn {Δ : TyCtx} : Ty Δ → Ty Δ → Set where
  []ᶜ : ∀ {A} → CastColumn A A
  _▻ᶜ_ : ∀ {A B C} {μ : Env∼ Δ}
    → μ ⊢ A ∼ B
    → CastColumn B C
    → CastColumn A C

columnSize : ∀ {Δ} {A B : Ty Δ}
  → CastColumn A B
  → ℕ
columnSize []ᶜ = zero
columnSize (c ▻ᶜ κ) = castSize c + columnSize κ

applyColumn : ∀ {Δ} {A B : Ty Δ}
  → Term Δ
  → CastColumn A B
  → Term Δ
applyColumn M []ᶜ = M
applyColumn M (c ▻ᶜ κ) = applyColumn (M ⟨ c ⟩) κ

mapColumn₁ : ∀ {Δ Δ′} {A B : Ty Δ}
  → (χ : StoreChange Δ Δ′)
  → CastColumn A B
  → CastColumn (applyTy χ A) (applyTy χ B)
mapColumn₁ χ []ᶜ = []ᶜ
mapColumn₁ χ (c ▻ᶜ κ) = applyConsistency χ c ▻ᶜ mapColumn₁ χ κ

mapColumn : ∀ {Δ Δ′} {A B : Ty Δ}
  → (χs : StoreChanges Δ Δ′)
  → CastColumn A B
  → CastColumn (applyTys χs A) (applyTys χs B)
mapColumn [] κ = κ
mapColumn (χ ∷ χs) κ = mapColumn χs (mapColumn₁ χ κ)

infixr 5 _++χ_

_++χ_ : ∀ {Δ Δ′ Δ″}
  → StoreChanges Δ Δ′
  → StoreChanges Δ′ Δ″
  → StoreChanges Δ Δ″
[] ++χ ψs = ψs
(χ ∷ χs) ++χ ψs = χ ∷ (χs ++χ ψs)

------------------------------------------------------------------------
-- Result and driver surfaces
------------------------------------------------------------------------

ValueCatchupRight² : Set
ValueCatchupRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (κ : CastColumn B B′)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (applyColumn M′ κ —↠[ χs ] N′)
        × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            ECR.transport⊑ᵂ ext q))

ExtraCastRightAt : ℕ → Set
ExtraCastRightAt fuel = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (c′ : ν ⊢ B ∼ B′)
  → castSize c′ < fuel
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ c′ ⟩ —↠[ χs ] N′)
        × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            ECR.transport⊑ᵂ ext q))

InstCatchupRightAt : ℕ → Set
InstCatchupRightAt fuel = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → AllValueView M′
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → castSize ((inst c′) B′≢★) < fuel
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
        × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            ECR.transport⊑ᵂ ext q))

ValueCatchupRightAt : ℕ → Set
ValueCatchupRightAt fuel = ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (κ : CastColumn B B′)
  → columnSize κ < fuel
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (applyColumn M′ κ —↠[ χs ] N′)
        × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            ECR.transport⊑ᵂ ext q))

record FuelKnot (fuel : ℕ) : Set₁ where
  field
    extra-cast-at : ExtraCastRightAt fuel
    inst-catchup-at : InstCatchupRightAt fuel
    value-catchup-at : ValueCatchupRightAt fuel

record FuelStepSurface (fuel : ℕ) : Set₁ where
  field
    smaller-extra :
      ∀ {m} → m < fuel → ExtraCastRightAt m
    smaller-inst :
      ∀ {m} → m < fuel → InstCatchupRightAt m
    smaller-value :
      ∀ {m} → m < fuel → ValueCatchupRightAt m
    next-knot : FuelKnot (suc fuel)

------------------------------------------------------------------------
-- Imported worker smoke tests
------------------------------------------------------------------------

module ImportedM4Smoke
    (inversion : RightInjInversion²)
    (inst-catchup : ECR.InstCatchupRight²)
  where
  ground-other-worker =
    ECRP.extra-cast-right-ground-other² inversion inst-catchup

  project-expand-worker =
    ECRP.extra-cast-right-project-expand² inversion inst-catchup

  inst-worker =
    ECRP.extra-cast-right-inst² inversion inst-catchup

  inst-canonical-worker =
    ECRP.extra-cast-right-inst-canonical² inversion inst-catchup

m5-step-catalog : ICRD.AllValueViewStepCatalogᵀ
m5-step-catalog = ICRP.all-value-view-step-catalog

------------------------------------------------------------------------
-- Strict-decrease obligations used by the knot
------------------------------------------------------------------------

ground-other-decrease : ∀ {Δ} {μ : Env∼ Δ} {A G : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    ⦃ Ans : NonStar A ⦄
  → (c : μ ⊢ A ∼ G)
  → castSize c < castSize (_! c)
ground-other-decrease c = n<1+n (castSize c)

project-expand-decrease : ∀ {Δ} {μ : Env∼ Δ} {G B : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : μ ⊢ G ∼ B)
  → castSize c < castSize (？ c)
project-expand-decrease c = n<1+n (castSize c)

postulate
  castSize-↑close-inst : ∀ {Δ} {ν : Env∼ Δ}
      {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ ν ⊢ A ∼ ⇑ᵗ B}
    → castSize (↑ᶜ (close-instᶜ c)) ≡ castSize c

inst-alloc-decrease : ∀ {Δ} {ν : Env∼ Δ}
    {A : Ty (suc Δ)} {B : Ty Δ}
    {c : instᵐ ν ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
  → (B≢★ : B ≢ ★)
  → castSize (↑ᶜ (close-instᶜ c)) < castSize ((inst c) B≢★)
inst-alloc-decrease {c = c} B≢★ rewrite castSize-↑close-inst {c = c} =
  n<1+n (castSize c)

postulate
  columnSize-map : ∀ {Δ Δ′} {A B : Ty Δ}
      (χs : StoreChanges Δ Δ′) (κ : CastColumn A B)
    → columnSize (mapColumn χs κ) ≡ columnSize κ

  composeWorldExtendᴿ : ∀ {Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₁ᵂ Δ₂ᵂ}
      {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
      {W₀ : World Δᴸ Δ₀ Δ}
      {W₁ : World Δᴸ Δ₁ Δ₁ᵂ}
      {W₂ : World Δᴸ Δ₂ Δ₂ᵂ}
    → ECR.WorldExtendᴿ χs W₀ W₁
    → ECR.WorldExtendᴿ ψs W₁ W₂
    → ECR.WorldExtendᴿ (χs ++χ ψs) W₀ W₂

  mapCtxᴿ-compose : ∀ {Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₁ᵂ Δ₂ᵂ}
      {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
      {W₀ : World Δᴸ Δ₀ Δ}
      {W₁ : World Δᴸ Δ₁ Δ₁ᵂ}
      {W₂ : World Δᴸ Δ₂ Δ₂ᵂ}
      (ext₁ : ECR.WorldExtendᴿ χs W₀ W₁)
      (ext₂ : ECR.WorldExtendᴿ ψs W₁ W₂)
      (γ : CtxImp W₀)
    → ECR.mapCtxᴿ ext₂ (ECR.mapCtxᴿ ext₁ γ) ≡
      ECR.mapCtxᴿ (composeWorldExtendᴿ ext₁ ext₂) γ

  composeReduction : ∀ {Δ₀ Δ₁ Δ₂}
      {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
      {M : Term Δ₀} {N : Term Δ₁} {P : Term Δ₂}
    → M —↠[ χs ] N
    → N —↠[ ψs ] P
    → M —↠[ χs ++χ ψs ] P

  liftReductionThroughColumn : ∀ {Δ Δ′} {A B : Ty Δ}
      {χs : StoreChanges Δ Δ′} {M : Term Δ} {N : Term Δ′}
    → (κ : CastColumn A B)
    → M —↠[ χs ] N
    → applyColumn M κ —↠[ χs ] applyColumn N (mapColumn χs κ)

------------------------------------------------------------------------
-- Concrete catalog two-cast column
------------------------------------------------------------------------

catalog-inst-then-function-column :
  CastColumn (RC.∀X⇒X {Δ = zero}) (RC.★⇒★ᵗ {Δ = zero})
catalog-inst-then-function-column =
  RC.∀X⇒X∼★⇒★ ▻ᶜ RC.★⇒★∼★⇒★ ▻ᶜ []ᶜ

catalog-inst-then-function-weight :
  columnSize catalog-inst-then-function-column ≡ 9
catalog-inst-then-function-weight = refl
