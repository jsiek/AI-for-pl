module Primitives where

-- File Charter:
--   * Constants and primitive operators for GTSFImp.
--   * Defines primitive syntax, primitive result types, primitive delta
--     evidence, and small type-renaming facts for constant types.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; suc; _+_)

open import Types

------------------------------------------------------------------------
-- Constants and primitive operators
------------------------------------------------------------------------

data Const : Set where
  κℕ : ℕ → Const

constTy : ∀ {Δ} → Const → Ty Δ
constTy (κℕ n) = ‵ `ℕ

data Prim : Set where
  addℕ : Prim

primTy : ∀ {Δ} → Prim → Ty Δ
primTy addℕ = ‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ

data δ : Prim → Const → Const → Const → Set where
  δ-add : ∀ {m n : ℕ}
    → δ addℕ (κℕ m) (κℕ n) (κℕ (m + n))

constTy-⇑ᵗ : ∀ {Δ} κ
  → constTy {suc Δ} κ ≡ ⇑ᵗ (constTy {Δ} κ)
constTy-⇑ᵗ (κℕ n) = refl

constTy-renameᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) κ
  → constTy {Δ′} κ ≡ renameᵗ ρ (constTy {Δ} κ)
constTy-renameᵗ ρ (κℕ n) = refl
