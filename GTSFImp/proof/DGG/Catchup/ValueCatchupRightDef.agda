module proof.DGG.Catchup.ValueCatchupRightDef where

-- File Charter:
--   * States the M6 value-catch-up foundation surface.
--   * Defines the derivation-indexed target-cast fuel bound and the
--     fuel-indexed worker interfaces for the eventual mutual driver.
--   * Follows all nine live conversion-wrapper constructors directly:
--     target-neutral, source-neutral/unmatched/matched, and paired cases.
--   * Provides Set-level statements for the world/context support lemmas
--     proved separately in FuelSupportProof.
--   * Depends only on core syntax/reduction, stage-1 DGG interfaces, and
--     the shared target value-spine view.

import Data.Fin as Fin
open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _⊢★∼_; _!; ？_; inst_; instᵐ;
   ↑ᶜ_; close-instᶜ)
open import proof.Consistency using (castSize) public
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using (StoreChanges; _—↠[_]_; []; _∷_)
open import proof.Reduction using (_++χ_)

import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Derivation target-cast fuel bound
------------------------------------------------------------------------

-- `TargetCastBound fuel rel` is the columnless replacement for the old
-- syntactic cast-column size premise: every target-side cast layer embedded in
-- the CTI derivation `rel` has cast size strictly below `fuel`.  Structural
-- CTI layers only replay the bound on their premises.

TargetCastBound : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → ℕ
  → W ∣ γ ⊢² M ⊑ M′ ∶ q
  → Set
TargetCastBound fuel (CTI2.x⊑x² x∈) = ⊤
TargetCastBound fuel (CTI2.ƛ⊑ƛ² rel) = TargetCastBound fuel rel
TargetCastBound fuel (CTI2.·⊑·² rel₁ rel₂) =
  TargetCastBound fuel rel₁ × TargetCastBound fuel rel₂
TargetCastBound fuel (CTI2.Λ⊑Λ² liftγ vV vV′ rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel (CTI2.Λ⊑² Anv z∈A liftγ vV M⊢ rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV M⊢ rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel (CTI2.•⊑•² p∀ rel q r) =
  TargetCastBound fuel rel
TargetCastBound fuel (CTI2.•⊑² p∀ rel q r) =
  TargetCastBound fuel rel
TargetCastBound fuel (CTI2.κ⊑κ² κ p) = ⊤
TargetCastBound fuel (CTI2.cast⊑cast² c c′ rel q) =
  castSize c′ < fuel × TargetCastBound fuel rel
TargetCastBound fuel (CTI2.⊑cast² c′ rel q) =
  castSize c′ < fuel × TargetCastBound fuel rel
TargetCastBound fuel (CTI2.⊑reveal² c′⊢ position-empty rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel (CTI2.⊑conceal² c′⊢ position-empty rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel (CTI2.cast⊑² c rel q) = TargetCastBound fuel rel
TargetCastBound fuel (CTI2.reveal⊑-neutral² c⊢ position-empty rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel
    (CTI2.reveal⊑-only² c⊢ position-present mark-eq
      target-unoccupied representation rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel
    (CTI2.reveal⊑² c⊢ position-present member representation mono rb
      sameγ rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel
    (CTI2.conceal⊑-neutral² c⊢ position-empty rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel
    (CTI2.conceal⊑² c⊢ position-present mark-eq target-unoccupied
      representation rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel
    (CTI2.reveal⊑reveal² c⊢ c′⊢ position-eq position-present
      representation mono rb sameγ rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel
    (CTI2.conceal⊑conceal² c⊢ c′⊢ position-eq position-present
      representation mono rb sameγ rel q) =
  TargetCastBound fuel rel
TargetCastBound fuel (CTI2.blame⊑² M′⊢ p) = ⊤
TargetCastBound fuel (CTI2.⊕⊑⊕² op rel₁ rel₂ r) =
  TargetCastBound fuel rel₁ × TargetCastBound fuel rel₂

------------------------------------------------------------------------
-- Result and driver surfaces
------------------------------------------------------------------------

-- Value catch-up now consumes the CTI derivation for the whole target term.
-- The derivation itself carries every target-side `⊑cast²`/`cast⊑cast²`
-- layer; fuel is tracked by `TargetCastBound`, not by a syntactic column.

ValueCatchupRight² : Set
ValueCatchupRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value M
  → W ∣ γ ⊢² M ⊑ M″ ∶ q
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M″ —↠[ χs ] N′)
        × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            ECR.transport⊑ᵂ ext q))

ExtraCastRightAt : ℕ → Set
ExtraCastRightAt fuel = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′ : ν ⊢ B ∼ B′)
  → castSize c′ < fuel
  → W ∣ γ ⊢² M ⊑ (M′ ⟨ c′ ⟩) ∶ q
  → Value M
  → Value M′
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

-- Residual cast consumers no longer carry a separate provenance judgment.
-- A stopped residual frame constructs the casted CTI premise directly.

ResidualCastBuilderᵀ : Set
ResidualCastBuilderᵀ = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′ : ν ⊢ B ∼ B′)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ γ ⊢² M ⊑ (M′ ⟨ c′ ⟩) ∶ q

residual-cast-builderᵀ : ResidualCastBuilderᵀ
residual-cast-builderᵀ {q = q} c′ rel = CTI2.⊑cast² c′ rel q

ValueCatchupRightAt : ℕ → Set
ValueCatchupRightAt fuel = ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value M
  → (rel : W ∣ γ ⊢² M ⊑ M″ ∶ q)
  → TargetCastBound fuel rel
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M″ —↠[ χs ] N′)
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

------------------------------------------------------------------------
-- Strict-decrease and support statements
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
