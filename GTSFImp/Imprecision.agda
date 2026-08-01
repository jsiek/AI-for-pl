module Imprecision where

-- File Charter:
--   * Defines type imprecision.

open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import Types

------------------------------------------------------------------------
-- One-context coercion-indexed narrowing and widening
------------------------------------------------------------------------

data VarImp : Set where
  X⊑X : VarImp
  X⊑★ : VarImp

ImpEnv : Set
ImpEnv = TyVar → VarImp

idᵐ : ImpEnv
idᵐ X = X⊑X

extᵐ : ImpEnv → ImpEnv
extᵐ μ zero = X⊑X
extᵐ μ (suc X) = μ X

instᵐ : ImpEnv → ImpEnv
instᵐ μ zero = X⊑★
instᵐ μ (suc X) = μ X

----------------------------------------------------------------------
-- Imprecision
----------------------------------------------------------------------

infix 4 _∣_⊢_⊑_

data _∣_⊢_⊑_ (Δ : TyCtx) (μ : ImpEnv)  : Ty → Ty → Set where

  ★⊑★ :
      -------------
      Δ ∣ μ ⊢ ★ ⊑ ★

  ι⊑ι : ∀ {ι}
      ---------------------
      → Δ ∣ μ ⊢ (‵ ι) ⊑ (‵ ι)

  X⊑X : ∀ {X}
      -------------------
    → Δ ∣ μ ⊢ ＇ X ⊑ ＇ X

  ⇒⊑⇒ : ∀ {A A′ B B′}
    → Δ ∣ μ ⊢ A ⊑ A′
    → Δ ∣ μ ⊢ B ⊑ B′
      ---------------------------
    → Δ ∣ μ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ∀⊑∀ : ∀ {A B}
    → suc Δ ∣ extᵐ μ ⊢ A ⊑ B
      -----------------------
    → Δ ∣ μ ⊢ (`∀ A) ⊑ (`∀ B)

  ⇒⊑★ : ∀ {A B} 
    → Δ ∣ μ ⊢ A ⊑ ★
    → Δ ∣ μ ⊢ B ⊑ ★
      -----------------
    → Δ ∣ μ ⊢ A ⇒ B ⊑ ★

  ι⊑★ : ∀ {ι} 
      ---------------
    → Δ ∣ μ ⊢ ‵ ι ⊑ ★

  X⊑★ : ∀ {X}
    → μ X ≡ X⊑★
      ----------------
    → Δ ∣ μ ⊢ ＇ X ⊑ ★

  ∀⊑ : ∀ {A B}
    → NonVar A
    → zero ∈ᵗ A
    → WfTy Δ B
    → suc Δ ∣ instᵐ μ ⊢ A ⊑ ⇑ᵗ B
      ---------------------------
    → Δ ∣ μ ⊢ (`∀ A) ⊑ B

infix 4 _⊢_⊑_

_⊢_⊑_ : TyCtx → Ty → Ty → Set
Δ ⊢ A ⊑ B = Δ ∣ idᵐ ⊢ A ⊑ B
