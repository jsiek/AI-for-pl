module Imprecision where

-- File Charter:
--   * Defines intrinsically scoped type imprecision.
--   * Includes the universal-ground and empty-universal clauses required
--     for consistency to coincide with existence of a common lower bound.

open import Data.Nat using (zero; suc)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types

private
  variable
    Δ : TyCtx

data VarImp : Set where
  X⊑X : VarImp
  X⊑★ : VarImp

ImpEnv : TyCtx → Set
ImpEnv Δ = TyVar Δ → VarImp

idᵐ : ∀ {Δ} → ImpEnv Δ
idᵐ X = X⊑X

extᵐ : ImpEnv Δ → ImpEnv (suc Δ)
extᵐ μ zero = X⊑X
extᵐ μ (suc X) = μ X

instᵐ : ImpEnv Δ → ImpEnv (suc Δ)
instᵐ μ zero = X⊑★
instᵐ μ (suc X) = μ X

----------------------------------------------------------------------
-- Imprecision
----------------------------------------------------------------------

infix 4 _⊢_⊑_

data _⊢_⊑_ {Δ : TyCtx} (μ : ImpEnv Δ) : Ty Δ → Ty Δ → Set where

  ★⊑★ :
      -------------
      μ ⊢ ★ ⊑ ★

  ι⊑ι : ∀ {ι}
      ---------------------
      → μ ⊢ (‵ ι) ⊑ (‵ ι)

  X⊑X : ∀ {X}
      -------------------
    → μ ⊢ ＇ X ⊑ ＇ X

  ⇒⊑⇒ : ∀ {A A′ B B′}
    → μ ⊢ A ⊑ A′
    → μ ⊢ B ⊑ B′
      ---------------------------
    → μ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ∀⊑∀ : ∀ {A B}
    → extᵐ μ ⊢ A ⊑ B
      -----------------------
    → μ ⊢ (`∀ A) ⊑ (`∀ B)

  ⇒⊑★ : ∀ {A B}
    → μ ⊢ A ⊑ ★
    → μ ⊢ B ⊑ ★
      -----------------
    → μ ⊢ A ⇒ B ⊑ ★

  ι⊑★ : ∀ {ι}
      ---------------
    → μ ⊢ ‵ ι ⊑ ★

  X⊑★ : ∀ {X}
    → μ X ≡ X⊑★
      ----------------
    → μ ⊢ ＇ X ⊑ ★

  ∀⊑ : ∀ {A B}
    → NonVar A
    → zero ∈ᵗ A
    → instᵐ μ ⊢ A ⊑ ⇑ᵗ B
      ---------------------------
    → μ ⊢ (`∀ A) ⊑ B

  ∀★⊑★ :
      ------------------
    μ ⊢ (`∀ ★) ⊑ ★

  bot-elim :
      --------------------------------
    μ ⊢ (`∀ (＇ zero)) ⊑ (`∀ ★)

  bot⊑★ :
      ---------------------------
    μ ⊢ (`∀ (＇ zero)) ⊑ ★

infix 4 _⊑_

_⊑_ : ∀ {Δ} → Ty Δ → Ty Δ → Set
A ⊑ B = idᵐ ⊢ A ⊑ B
