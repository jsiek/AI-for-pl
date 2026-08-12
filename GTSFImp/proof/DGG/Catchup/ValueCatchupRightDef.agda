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
open import CastTerms using (Term; Value; Inert; _⟨_⟩)
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

------------------------------------------------------------------------
-- Catch-up provenance for columns
------------------------------------------------------------------------

-- A provenance-FREE value catch-up surface over arbitrary columns is
-- refuted: the projection-mismatch package feeds it a singleton
-- projection column and the target blames (checked:
-- notes/ValueCatchupProvenanceGapScratch.agda; design:
-- notes/M6-PROVENANCE-DESIGN.md). The driver therefore carries a
-- column provenance: a full CatchupCast at the head (which faces the
-- real current value) and the term-independent fragment CatchupCast⁻
-- in the tail. Only CatchupCast's projection constructors inspect the
-- target term, so the fragment embeds at ANY term (catchup⁻-embed in
-- ColumnSupportProof) and the driver re-heads the tail at each newly
-- produced value.

data CatchupCast⁻ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} :
    ∀ {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B
    → ν ⊢ B ∼ B′
    → A ⊑ᵂ⟨ W ⟩ B′
    → Set where

  catchup⁻-inert : ∀ {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B} {c′ : ν ⊢ B ∼ B′}
      {q : A ⊑ᵂ⟨ W ⟩ B′}
    → Inert c′
    → CatchupCast⁻ p c′ q

  catchup⁻-id : ∀ {B : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B}
    → (a : Atom B)
    → CatchupCast⁻ p (id {μ = ν} a) q

  catchup⁻-ground-other : ∀ {B G : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B}
      {Gᵍ : Ground G} {G∼★ : ν ⊢ G ∼★}
      {Bns : NonStar B}
      {c : ν ⊢ B ∼ G} {q : A ⊑ᵂ⟨ W ⟩ ★}
    → B ≢ G
    → (r : A ⊑ᵂ⟨ W ⟩ G)
    → CatchupCast⁻ {W = W} {A = A} p c r
    → CatchupCast⁻ p
        (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄)
        q

  catchup⁻-inst : ∀ {B₀ : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
      {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B₀}
      {c′ : instᵐ ν ⊢ B₀ ∼ ⇑ᵗ B′}
      ⦃ Bnv : NonVar B₀ ⦄ ⦃ zero∈B : Fin.zero ∈ᵗ B₀ ⦄
      {B′≢★ : B′ ≢ ★} {q : A ⊑ᵂ⟨ W ⟩ B′}
    → CatchupCast⁻ p ((inst c′) B′≢★) q

  catchup⁻-bot-elim : ∀ {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ `∀ (＇ Fin.zero)}
      {q : A ⊑ᵂ⟨ W ⟩ `∀ ★}
    → CatchupCast⁻ p (bot-elim {μ = ν}) q

  catchup⁻-bot-intro : ∀ {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ `∀ ★}
      {q : A ⊑ᵂ⟨ W ⟩ `∀ (＇ Fin.zero)}
    → CatchupCast⁻ p (bot-intro {μ = ν}) q

data CatchupColumn⁻ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} :
    ∀ {B B′ : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B
    → CastColumn B B′
    → A ⊑ᵂ⟨ W ⟩ B′
    → Set where
  ccol⁻-[] : ∀ {B : Ty Δᴿ} {q : A ⊑ᵂ⟨ W ⟩ B}
    → CatchupColumn⁻ q []ᶜ q
  ccol⁻-▻ : ∀ {B B₁ B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {q₀ : A ⊑ᵂ⟨ W ⟩ B} {q₁ : A ⊑ᵂ⟨ W ⟩ B₁}
      {q′ : A ⊑ᵂ⟨ W ⟩ B′}
      {c : ν ⊢ B ∼ B₁} {κ : CastColumn B₁ B′}
    → CatchupCast⁻ {W = W} {A = A} q₀ c q₁
    → CatchupColumn⁻ {W = W} {A = A} q₁ κ q′
    → CatchupColumn⁻ q₀ (c ▻ᶜ κ) q′

data CatchupColumn {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ}
    (M′ : Term Δᴿ) :
    ∀ {B B′ : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B
    → CastColumn B B′
    → A ⊑ᵂ⟨ W ⟩ B′
    → Set where
  ccol-[] : ∀ {B : Ty Δᴿ} {q : A ⊑ᵂ⟨ W ⟩ B}
    → CatchupColumn M′ q []ᶜ q
  ccol-▻ : ∀ {B B₁ B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
      {p : A ⊑ᵂ⟨ W ⟩ B} {q₁ : A ⊑ᵂ⟨ W ⟩ B₁}
      {q : A ⊑ᵂ⟨ W ⟩ B′}
      {c : ν ⊢ B ∼ B₁} {κ : CastColumn B₁ B′}
    → ECR.CatchupCast {W = W} {A = A} p M′ c q₁
    → CatchupColumn⁻ {W = W} {A = A} q₁ κ q
    → CatchupColumn M′ p (c ▻ᶜ κ) q

-- Fragment embedding: provenance for any target term (proved in
-- ColumnSupportProof).

Catchup⁻Embedᵀ : Set
Catchup⁻Embedᵀ = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {c′ : ν ⊢ B ∼ B′}
    {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (N : Term Δᴿ)
  → CatchupCast⁻ {W = W} {A = A} p c′ q
  → ECR.CatchupCast {W = W} {A = A} p N c′ q

-- Fragment transport along a right world extension, cast side mapped
-- by the store changes (M6 driver deliverable).

CatchupColumn⁻Transportᵀ : Set
CatchupColumn⁻Transportᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′W}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′W}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {q₀ : A ⊑ᵂ⟨ W ⟩ B} {q′ : A ⊑ᵂ⟨ W ⟩ B′}
    {κ : CastColumn B B′}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → CatchupColumn⁻ {W = W} {A = A} q₀ κ q′
  → CatchupColumn⁻ {W = W′} {A = A} (ECR.transport⊑ᵂ ext q₀)
      (mapColumn χs κ) (ECR.transport⊑ᵂ ext q′)

------------------------------------------------------------------------
-- Driver surface
------------------------------------------------------------------------

ValueCatchupRightProv² : Set
ValueCatchupRightProv² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (κ : CastColumn B B′)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → CatchupColumn {W = W} {A = A} M′ p κ q
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

ValueCatchupRightProvAt : ℕ → Set
ValueCatchupRightProvAt fuel = ∀ {Δᴸ Δᴿ Δ}
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
  → CatchupColumn {W = W} {A = A} M′ p κ q
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
    value-catchup-at : ValueCatchupRightProvAt fuel

record FuelStepSurface (fuel : ℕ) : Set₁ where
  field
    smaller-extra : ∀ {m} → m < fuel → ExtraCastRightAt m
    smaller-inst : ∀ {m} → m < fuel → InstCatchupRightAt m
    smaller-value : ∀ {m} → m < fuel → ValueCatchupRightProvAt m
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
