module proof.NuCore.Relations.NuImprecisionTermContextDef where

-- File Charter:
--   * Defines term-context imprecision and its left/right typing projections.
--   * Defines matched and one-sided type-binder lifts and lookup projection.
--   * Excludes relational stores, term imprecision, simulation, and proof
--     assembly.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (cong)

open import Ctx using (⤊ᵗ)
open import ImprecisionComposition using (⌊_⌋)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Types using
  (Ctx; Ty; TyCtx; _∋_⦂_; S; Z; ⇑ᵗ)


variable
  Φ Ψ : ImpCtx
  Δᴸ Δᴿ : TyCtx


record CtxImpEntry (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) : Set where
  constructor ctx-imp
  field
    srcTyⁱ : Ty
    tgtTyⁱ : Ty
    impTyⁱ : Φ ∣ Δᴸ ⊢ srcTyⁱ ⊑ tgtTyⁱ ⊣ Δᴿ

open CtxImpEntry public


CtxImp : ImpCtx → TyCtx → TyCtx → Set
CtxImp Φ Δᴸ Δᴿ = List (CtxImpEntry Φ Δᴸ Δᴿ)


leftCtxⁱ : CtxImp Φ Δᴸ Δᴿ → Ctx
leftCtxⁱ = map srcTyⁱ


rightCtxⁱ : CtxImp Φ Δᴸ Δᴿ → Ctx
rightCtxⁱ = map tgtTyⁱ


data LiftCtxⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    CtxImp Φ Δᴸ Δᴿ → CtxImp Ψ (suc Δᴸ) (suc Δᴿ) → Set where
  lift-ctx-[] :
    LiftCtxⁱ Ψ [] []

  lift-ctx-∷ : ∀ {γ γ′ A B p p′}
    → ⌊ p′ ⌋ ≡ ⌊ p ⌋
    → LiftCtxⁱ Ψ γ γ′
      --------------------------------------------------------------
    → LiftCtxⁱ Ψ
        (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) (⇑ᵗ B) p′ ∷ γ′)


leftCtxⁱ-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftCtxⁱ Ψ γ γ′ →
  leftCtxⁱ γ′ ≡ ⤊ᵗ (leftCtxⁱ γ)
leftCtxⁱ-lift lift-ctx-[] = refl
leftCtxⁱ-lift (lift-ctx-∷ _ liftγ) =
  cong (_ ∷_) (leftCtxⁱ-lift liftγ)


rightCtxⁱ-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftCtxⁱ Ψ γ γ′ →
  rightCtxⁱ γ′ ≡ ⤊ᵗ (rightCtxⁱ γ)
rightCtxⁱ-lift lift-ctx-[] = refl
rightCtxⁱ-lift (lift-ctx-∷ _ liftγ) =
  cong (_ ∷_) (rightCtxⁱ-lift liftγ)


data LiftLeftCtxⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    CtxImp Φ Δᴸ Δᴿ → CtxImp Ψ (suc Δᴸ) Δᴿ → Set where
  lift-left-ctx-[] :
    LiftLeftCtxⁱ Ψ [] []

  lift-left-ctx-∷ : ∀ {γ γ′ A B p p′}
    → ⌊ p′ ⌋ ≡ ⌊ p ⌋
    → LiftLeftCtxⁱ Ψ γ γ′
      --------------------------------------------------------------
    → LiftLeftCtxⁱ Ψ
        (ctx-imp A B p ∷ γ)
        (ctx-imp (⇑ᵗ A) B p′ ∷ γ′)


leftCtxⁱ-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftCtxⁱ Ψ γ γ′ →
  leftCtxⁱ γ′ ≡ ⤊ᵗ (leftCtxⁱ γ)
leftCtxⁱ-lift-left lift-left-ctx-[] = refl
leftCtxⁱ-lift-left (lift-left-ctx-∷ _ liftγ) =
  cong (_ ∷_) (leftCtxⁱ-lift-left liftγ)


rightCtxⁱ-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftCtxⁱ Ψ γ γ′ →
  rightCtxⁱ γ′ ≡ rightCtxⁱ γ
rightCtxⁱ-lift-left lift-left-ctx-[] = refl
rightCtxⁱ-lift-left (lift-left-ctx-∷ _ liftγ) =
  cong (_ ∷_) (rightCtxⁱ-lift-left liftγ)


data LiftRightCtxⁱ {Φ Δᴸ Δᴿ} (Ψ : ImpCtx) :
    CtxImp Φ Δᴸ Δᴿ → CtxImp Ψ Δᴸ (suc Δᴿ) → Set where
  lift-right-ctx-[] :
    LiftRightCtxⁱ Ψ [] []

  lift-right-ctx-∷ : ∀ {γ γ′ A B p p′}
    → ⌊ p′ ⌋ ≡ ⌊ p ⌋
    → LiftRightCtxⁱ Ψ γ γ′
      --------------------------------------------------------------
    → LiftRightCtxⁱ Ψ
        (ctx-imp A B p ∷ γ)
        (ctx-imp A (⇑ᵗ B) p′ ∷ γ′)


leftCtxⁱ-lift-right :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ (suc Δᴿ)} →
  LiftRightCtxⁱ Ψ γ γ′ →
  leftCtxⁱ γ′ ≡ leftCtxⁱ γ
leftCtxⁱ-lift-right lift-right-ctx-[] = refl
leftCtxⁱ-lift-right (lift-right-ctx-∷ _ liftγ) =
  cong (_ ∷_) (leftCtxⁱ-lift-right liftγ)


rightCtxⁱ-lift-right :
  ∀ {Φ Δᴸ Δᴿ Ψ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ (suc Δᴿ)} →
  LiftRightCtxⁱ Ψ γ γ′ →
  rightCtxⁱ γ′ ≡ ⤊ᵗ (rightCtxⁱ γ)
rightCtxⁱ-lift-right lift-right-ctx-[] = refl
rightCtxⁱ-lift-right (lift-right-ctx-∷ _ liftγ) =
  cong (_ ∷_) (rightCtxⁱ-lift-right liftγ)


leftCtxⁱ-∋ :
  ∀ {Φ Δᴸ Δᴿ γ x A B p} →
  γ ∋ x ⦂ ctx-imp A B p →
  leftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} γ ∋ x ⦂ A
leftCtxⁱ-∋ Z = Z
leftCtxⁱ-∋ (S x∈) = S (leftCtxⁱ-∋ x∈)


rightCtxⁱ-∋ :
  ∀ {Φ Δᴸ Δᴿ γ x A B p} →
  γ ∋ x ⦂ ctx-imp A B p →
  rightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} γ ∋ x ⦂ B
rightCtxⁱ-∋ Z = Z
rightCtxⁱ-∋ (S x∈) = S (rightCtxⁱ-∋ x∈)
