module proof.DGG.Catchup.ValueCatchupRightDef where

-- File Charter:
--   * States the M6 value-catch-up foundation surface.
--   * Defines target cast columns, their structural cast measure, and
--     fuel-indexed worker interfaces for the eventual mutual driver.
--   * Provides Set-level statements for the column support lemmas proved
--     separately in ColumnSupportProof.
--   * Depends only on core syntax/reduction, stage-1 DGG interfaces, and
--     the shared target value-spine view.

import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; id; _↦_; ∀ᶜ_;
   _!; ？_; inst_; gen_; instᵐ; ↑ᶜ_; close-instᶜ;
   bot-elim; bot-intro)
open import proof.Consistency using (castSize) public
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using
  (StoreChange; StoreChanges; _—↠[_]_; []; _∷_;
   applyTy; applyTys; applyConsistency)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Cast columns
------------------------------------------------------------------------

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

-- WARNING: refuted as stated — an arbitrary CastColumn with no
-- per-cast CatchupCast provenance admits the projection-mismatch
-- package (checked: ValueCatchupProvenanceGapScratch.agda at the repo
-- root). The M6 driver milestone will replace this surface with a
-- provenance-carrying statement. Kept for interface reference only;
-- do not attempt to inhabit.
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
  → ECR.CatchupCast {W = W} {A = A} p M′ c′ q
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

-- WARNING: refuted as stated — an arbitrary CastColumn with no
-- per-cast CatchupCast provenance admits the projection-mismatch
-- package (checked: ValueCatchupProvenanceGapScratch.agda at the repo
-- root). The M6 driver milestone will replace this surface with a
-- provenance-carrying statement. Kept for interface reference only;
-- do not attempt to inhabit.
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
    smaller-extra : ∀ {m} → m < fuel → ExtraCastRightAt m
    smaller-inst : ∀ {m} → m < fuel → InstCatchupRightAt m
    smaller-value : ∀ {m} → m < fuel → ValueCatchupRightAt m
    next-knot : FuelKnot (suc fuel)

------------------------------------------------------------------------
-- Strict-decrease and column-support statements
------------------------------------------------------------------------

ground-other-decreaseᵀ : Set
ground-other-decreaseᵀ = ∀ {Δ} {μ : Env∼ Δ} {A G : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
    ⦃ Ans : NonStar A ⦄
  → (c : μ ⊢ A ∼ G)
  → castSize c < castSize (_! c)

project-expand-decreaseᵀ : Set
project-expand-decreaseᵀ = ∀ {Δ} {μ : Env∼ Δ} {G B : Ty Δ}
    ⦃ Gᵍ : Ground G ⦄ ⦃ ★∼G : μ ⊢★∼ G ⦄
    ⦃ Bns : NonStar B ⦄
  → (c : μ ⊢ G ∼ B)
  → castSize c < castSize (？ c)

castSize-↑close-instᵀ : Set
-- Equality was refuted; see
-- m6-foundation-castSize-↑close-inst-blocked.red.
castSize-↑close-instᵀ = ∀ {Δ} {ν : Env∼ Δ}
    {A : Ty (suc Δ)} {B : Ty Δ}
    {c : instᵐ ν ⊢ A ∼ ⇑ᵗ B}
  → castSize (↑ᶜ (close-instᶜ c)) ≤ castSize c

inst-alloc-decreaseᵀ : Set
inst-alloc-decreaseᵀ = ∀ {Δ} {ν : Env∼ Δ}
    {A : Ty (suc Δ)} {B : Ty Δ}
    {c : instᵐ ν ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
  → (B≢★ : B ≢ ★)
  → castSize (↑ᶜ (close-instᶜ c)) < castSize ((inst c) B≢★)

columnSize-mapᵀ : Set
columnSize-mapᵀ = ∀ {Δ Δ′} {A B : Ty Δ}
  → (χs : StoreChanges Δ Δ′)
  → (κ : CastColumn A B)
  → columnSize (mapColumn χs κ) ≡ columnSize κ

composeWorldExtendᴿᵀ : Set
composeWorldExtendᴿᵀ = ∀ {Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₁ᵂ Δ₂ᵂ}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {W₀ : World Δᴸ Δ₀ Δ}
    {W₁ : World Δᴸ Δ₁ Δ₁ᵂ}
    {W₂ : World Δᴸ Δ₂ Δ₂ᵂ}
  → ECR.WorldExtendᴿ χs W₀ W₁
  → ECR.WorldExtendᴿ ψs W₁ W₂
  → ECR.WorldExtendᴿ (χs ++χ ψs) W₀ W₂

mapCtxᴿ-composeᵀ : composeWorldExtendᴿᵀ → Set
mapCtxᴿ-composeᵀ composeWorldExtendᴿ =
  ∀ {Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₁ᵂ Δ₂ᵂ}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {W₀ : World Δᴸ Δ₀ Δ}
    {W₁ : World Δᴸ Δ₁ Δ₁ᵂ}
    {W₂ : World Δᴸ Δ₂ Δ₂ᵂ}
    (ext₁ : ECR.WorldExtendᴿ χs W₀ W₁)
    (ext₂ : ECR.WorldExtendᴿ ψs W₁ W₂)
    (γ : CtxImp W₀)
  → ECR.mapCtxᴿ ext₂ (ECR.mapCtxᴿ ext₁ γ) ≡
    ECR.mapCtxᴿ (composeWorldExtendᴿ ext₁ ext₂) γ

composeReductionᵀ : Set
composeReductionᵀ = ∀ {Δ₀ Δ₁ Δ₂}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {M : Term Δ₀} {N : Term Δ₁} {P : Term Δ₂}
  → M —↠[ χs ] N
  → N —↠[ ψs ] P
  → M —↠[ χs ++χ ψs ] P

liftReductionThroughColumnᵀ : Set
liftReductionThroughColumnᵀ = ∀ {Δ Δ′} {A B : Ty Δ}
    {χs : StoreChanges Δ Δ′} {M : Term Δ} {N : Term Δ′}
  → (κ : CastColumn A B)
  → M —↠[ χs ] N
  → applyColumn M κ —↠[ χs ] applyColumn N (mapColumn χs κ)
