module proof.MlbTypeTest where

-- File Charter:
--   * Regression examples for the computational part of GTSF maximal lower
--     bound selection.
--   * Exercises positive and negative `mlb?` cases, including forall-binder
--     merging, equation clashes, and incompatible type shapes.
--   * No general metatheory belongs here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe using (just; nothing)

open import Types
open import proof.MaximalLowerBounds
  using (mlb?)

------------------------------------------------------------------------
-- Concrete named example
------------------------------------------------------------------------

A : Ty
A = `∀ (★ ⇒ ＇ 0 ⇒ ★ ⇒ ★)

B : Ty
B = `∀ (＇ 0 ⇒ ★ ⇒ ★ ⇒ ＇ 0)

C : Ty
C = `∀ (`∀ (`∀ (＇ 2 ⇒ ＇ 0 ⇒ ＇ 1 ⇒ ＇ 2)))

Expected : Ty
Expected = `∀ (`∀ (＇ 1 ⇒ ＇ 0 ⇒ ★ ⇒ ＇ 1))

mlb?-returns-expected : mlb? A B ≡ just Expected
mlb?-returns-expected = refl

mlb?-base-base :
  mlb? (‵ `ℕ) (‵ `ℕ) ≡ just (‵ `ℕ)
mlb?-base-base = refl

mlb?-base-star :
  mlb? (‵ `𝔹) ★ ≡ just (‵ `𝔹)
mlb?-base-star = refl

mlb?-star-base :
  mlb? ★ (‵ `ℕ) ≡ just (‵ `ℕ)
mlb?-star-base = refl

mlb?-star-arrow :
  mlb? ★ ((‵ `ℕ) ⇒ (‵ `𝔹)) ≡ just ((‵ `ℕ) ⇒ (‵ `𝔹))
mlb?-star-arrow = refl

mlb?-arrow-arrow :
  mlb? ((‵ `ℕ) ⇒ ★) (★ ⇒ (‵ `𝔹)) ≡ just ((‵ `ℕ) ⇒ (‵ `𝔹))
mlb?-arrow-arrow = refl

mlb?-deduplicates-repeated-eqn :
  mlb? ((＇ 0) ⇒ (＇ 0)) ((＇ 0) ⇒ (＇ 0)) ≡
  just ((＇ 0) ⇒ (＇ 0))
mlb?-deduplicates-repeated-eqn = refl

mlb?-forall-var-var :
  mlb? (`∀ (＇ 0)) (`∀ (＇ 0)) ≡ just (`∀ (＇ 0))
mlb?-forall-var-var = refl

mlb?-forall-left-star :
  mlb? (`∀ (＇ 0)) ★ ≡ just (`∀ (＇ 0))
mlb?-forall-left-star = refl

mlb?-forall-unmatched-binders :
  mlb? (`∀ ((＇ 0) ⇒ ★)) (`∀ (★ ⇒ (＇ 0))) ≡
  just (`∀ (`∀ ((＇ 0) ⇒ (＇ 1))))
mlb?-forall-unmatched-binders = refl

mlb?-rejects-base-mismatch :
  mlb? (‵ `ℕ) (‵ `𝔹) ≡ nothing
mlb?-rejects-base-mismatch = refl

mlb?-rejects-equation-clash :
  mlb? ((＇ 0) ⇒ (＇ 0)) ((＇ 0) ⇒ (＇ 1)) ≡ nothing
mlb?-rejects-equation-clash = refl
