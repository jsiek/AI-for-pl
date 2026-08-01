module Primitives where

-- File Charter:
--   * Constants and primitive operators for GTSFImp.
--   * Defines primitive syntax, primitive result types, primitive delta
--     evidence, and small type-renaming facts for constant types.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; _∧_)
open import Data.Nat using (ℕ; suc; _+_)

open import Types

------------------------------------------------------------------------
-- Constants and primitive operators
------------------------------------------------------------------------

data Const : Set where
  κℕ : ℕ → Const
  κ𝔹 : Bool → Const

constTy : ∀ {Δ} → Const → Ty Δ
constTy (κℕ n) = ‵ `ℕ
constTy (κ𝔹 b) = ‵ `𝔹

data Prim : Set where
  addℕ : Prim
  and𝔹 : Prim

primArgTy : ∀ {Δ} → Prim → Ty Δ
primArgTy addℕ = ‵ `ℕ
primArgTy and𝔹 = ‵ `𝔹

primResultTy : ∀ {Δ} → Prim → Ty Δ
primResultTy addℕ = ‵ `ℕ
primResultTy and𝔹 = ‵ `𝔹

primTy : ∀ {Δ} → Prim → Ty Δ
primTy op = primArgTy op ⇒ primArgTy op ⇒ primResultTy op

data δ : Prim → Const → Const → Const → Set where
  δ-add : ∀ {m n : ℕ}
    → δ addℕ (κℕ m) (κℕ n) (κℕ (m + n))

  δ-and : ∀ {b c : Bool}
    → δ and𝔹 (κ𝔹 b) (κ𝔹 c) (κ𝔹 (b ∧ c))

constTy-⇑ᵗ : ∀ {Δ} κ
  → constTy {suc Δ} κ ≡ ⇑ᵗ (constTy {Δ} κ)
constTy-⇑ᵗ (κℕ n) = refl
constTy-⇑ᵗ (κ𝔹 b) = refl

constTy-renameᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) κ
  → constTy {Δ′} κ ≡ renameᵗ ρ (constTy {Δ} κ)
constTy-renameᵗ ρ (κℕ n) = refl
constTy-renameᵗ ρ (κ𝔹 b) = refl
