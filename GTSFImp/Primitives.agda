module Primitives where

-- File Charter:
--   * Constants and primitive operators for PolyConvert.
--   * Defines primitive syntax, primitive result types, primitive delta
--     evidence, and small type-renaming facts for constant types.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; _+_)

open import Types

------------------------------------------------------------------------
-- Constants and primitive operators
------------------------------------------------------------------------

data Const : Set where
  κℕ : ℕ → Const

constTy : Const → Ty
constTy (κℕ n) = ‵ `ℕ

data Prim : Set where
  addℕ : Prim

primTy : Prim → Ty
primTy addℕ = ‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ

data δ : Prim → Const → Const → Const → Set where
  δ-add : {m n : ℕ} →
          δ addℕ (κℕ m) (κℕ n) (κℕ (m + n))

constTy-⇑ᵗ : ∀ κ → constTy κ ≡ ⇑ᵗ (constTy κ)
constTy-⇑ᵗ (κℕ n) = refl

constTy-renameᵗ : ∀ ρ κ → constTy κ ≡ renameᵗ ρ (constTy κ)
constTy-renameᵗ ρ (κℕ n) = refl
