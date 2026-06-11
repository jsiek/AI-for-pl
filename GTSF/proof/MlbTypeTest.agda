module proof.MlbTypeTest where

-- File Charter:
--   * Regression examples for the computational part of GTSF maximal lower
--     bound selection.
--   * Exercises positive and negative `mlb?` cases, including forall-binder
--     merging, equation clashes, and incompatible type shapes.
--   * No general metatheory belongs here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (Dec; yes; no)

open import Imprecision using (idᵢ)
open import Types
open import proof.ImprecisionProperties using (imp?)
open import proof.MaximalLowerBounds
  using (mlb?)

is-yes : ∀ {P : Set} → Dec P → Bool
is-yes (yes _) = true
is-yes (no _) = false

imp?-accepts : TyCtx → Ty → Ty → Bool
imp?-accepts Δ A B = is-yes (imp? (idᵢ Δ) A B)

MlbResultLowerLeft? : TyCtx → Ty → Ty → Bool
MlbResultLowerLeft? Δ A B with mlb? A B
MlbResultLowerLeft? Δ A B | just C = imp?-accepts Δ C A
MlbResultLowerLeft? Δ A B | nothing = false

MlbResultLowerRight? : TyCtx → Ty → Ty → Bool
MlbResultLowerRight? Δ A B with mlb? A B
MlbResultLowerRight? Δ A B | just C = imp?-accepts Δ C B
MlbResultLowerRight? Δ A B | nothing = false

------------------------------------------------------------------------
-- Concrete named example
------------------------------------------------------------------------

A : Ty
A = `∀ (★ ⇒ ＇ 0 ⇒ ★ ⇒ ★)

B : Ty
B = `∀ (＇ 0 ⇒ ★ ⇒ ★ ⇒ ＇ 0)

Expected : Ty
Expected = `∀ (`∀ (＇ 1 ⇒ ＇ 0 ⇒ ★ ⇒ ＇ 1))

mlb?-returns-expected : mlb? A B ≡ just Expected
mlb?-returns-expected = refl

mlb?-returns-expected-lower-left : MlbResultLowerLeft? 0 A B ≡ true
mlb?-returns-expected-lower-left = refl

mlb?-returns-expected-lower-right : MlbResultLowerRight? 0 A B ≡ true
mlb?-returns-expected-lower-right = refl

mlb?-base-base :
  mlb? (‵ `ℕ) (‵ `ℕ) ≡ just (‵ `ℕ)
mlb?-base-base = refl

mlb?-base-base-lower-left : MlbResultLowerLeft? 0 (‵ `ℕ) (‵ `ℕ) ≡ true
mlb?-base-base-lower-left = refl

mlb?-base-base-lower-right : MlbResultLowerRight? 0 (‵ `ℕ) (‵ `ℕ) ≡ true
mlb?-base-base-lower-right = refl

mlb?-base-star :
  mlb? (‵ `𝔹) ★ ≡ just (‵ `𝔹)
mlb?-base-star = refl

mlb?-base-star-lower-left : MlbResultLowerLeft? 0 (‵ `𝔹) ★ ≡ true
mlb?-base-star-lower-left = refl

mlb?-base-star-lower-right : MlbResultLowerRight? 0 (‵ `𝔹) ★ ≡ true
mlb?-base-star-lower-right = refl

mlb?-star-base :
  mlb? ★ (‵ `ℕ) ≡ just (‵ `ℕ)
mlb?-star-base = refl

mlb?-star-base-lower-left : MlbResultLowerLeft? 0 ★ (‵ `ℕ) ≡ true
mlb?-star-base-lower-left = refl

mlb?-star-base-lower-right : MlbResultLowerRight? 0 ★ (‵ `ℕ) ≡ true
mlb?-star-base-lower-right = refl

mlb?-star-arrow :
  mlb? ★ ((‵ `ℕ) ⇒ (‵ `𝔹)) ≡ just ((‵ `ℕ) ⇒ (‵ `𝔹))
mlb?-star-arrow = refl

mlb?-star-arrow-lower-left :
  MlbResultLowerLeft? 0 ★ ((‵ `ℕ) ⇒ (‵ `𝔹)) ≡ true
mlb?-star-arrow-lower-left = refl

mlb?-star-arrow-lower-right :
  MlbResultLowerRight? 0 ★ ((‵ `ℕ) ⇒ (‵ `𝔹)) ≡ true
mlb?-star-arrow-lower-right = refl

mlb?-arrow-arrow :
  mlb? ((‵ `ℕ) ⇒ ★) (★ ⇒ (‵ `𝔹)) ≡ just ((‵ `ℕ) ⇒ (‵ `𝔹))
mlb?-arrow-arrow = refl

mlb?-arrow-arrow-lower-left :
  MlbResultLowerLeft? 0 ((‵ `ℕ) ⇒ ★) (★ ⇒ (‵ `𝔹)) ≡ true
mlb?-arrow-arrow-lower-left = refl

mlb?-arrow-arrow-lower-right :
  MlbResultLowerRight? 0 ((‵ `ℕ) ⇒ ★) (★ ⇒ (‵ `𝔹)) ≡ true
mlb?-arrow-arrow-lower-right = refl

mlb?-deduplicates-repeated-eqn :
  mlb? ((＇ 0) ⇒ (＇ 0)) ((＇ 0) ⇒ (＇ 0)) ≡
  just ((＇ 0) ⇒ (＇ 0))
mlb?-deduplicates-repeated-eqn = refl

mlb?-deduplicates-repeated-eqn-lower :
  MlbResultLowerLeft? 1 ((＇ 0) ⇒ (＇ 0)) ((＇ 0) ⇒ (＇ 0)) ≡ true
mlb?-deduplicates-repeated-eqn-lower = refl

mlb?-deduplicates-repeated-eqn-lower-right :
  MlbResultLowerRight? 1 ((＇ 0) ⇒ (＇ 0)) ((＇ 0) ⇒ (＇ 0)) ≡ true
mlb?-deduplicates-repeated-eqn-lower-right = refl

mlb?-forall-var-var :
  mlb? (`∀ (＇ 0)) (`∀ (＇ 0)) ≡ just (`∀ (＇ 0))
mlb?-forall-var-var = refl

mlb?-forall-var-var-lower :
  MlbResultLowerLeft? 0 (`∀ (＇ 0)) (`∀ (＇ 0)) ≡ true
mlb?-forall-var-var-lower = refl

mlb?-forall-var-var-lower-right :
  MlbResultLowerRight? 0 (`∀ (＇ 0)) (`∀ (＇ 0)) ≡ true
mlb?-forall-var-var-lower-right = refl

mlb?-forall-left-star :
  mlb? (`∀ (＇ 0)) ★ ≡ just (`∀ (＇ 0))
mlb?-forall-left-star = refl

mlb?-forall-left-star-lower : MlbResultLowerLeft? 0 (`∀ (＇ 0)) ★ ≡ true
mlb?-forall-left-star-lower = refl

mlb?-forall-left-star-lower-right :
  MlbResultLowerRight? 0 (`∀ (＇ 0)) ★ ≡ true
mlb?-forall-left-star-lower-right = refl

mlb?-forall-unmatched-binders :
  mlb? (`∀ ((＇ 0) ⇒ ★)) (`∀ (★ ⇒ (＇ 0))) ≡
  just (`∀ (`∀ ((＇ 0) ⇒ (＇ 1))))
mlb?-forall-unmatched-binders = refl

mlb?-forall-unmatched-binders-lower :
  MlbResultLowerLeft? 0 (`∀ ((＇ 0) ⇒ ★)) (`∀ (★ ⇒ (＇ 0))) ≡ true
mlb?-forall-unmatched-binders-lower = refl

mlb?-forall-unmatched-binders-lower-right :
  MlbResultLowerRight? 0 (`∀ ((＇ 0) ⇒ ★)) (`∀ (★ ⇒ (＇ 0))) ≡ true
mlb?-forall-unmatched-binders-lower-right = refl

mlb?-right-unmatched-before-matched :
  mlb? (`∀ (★ ⇒ (＇ 0))) (`∀ (`∀ ((＇ 0) ⇒ (＇ 1)))) ≡
  just (`∀ (`∀ ((＇ 0) ⇒ (＇ 1))))
mlb?-right-unmatched-before-matched = refl

mlb?-right-unmatched-before-matched-lower-left :
  MlbResultLowerLeft? 0 (`∀ (★ ⇒ (＇ 0)))
    (`∀ (`∀ ((＇ 0) ⇒ (＇ 1)))) ≡ true
mlb?-right-unmatched-before-matched-lower-left = refl

mlb?-right-unmatched-before-matched-lower-right :
  MlbResultLowerRight? 0 (`∀ (★ ⇒ (＇ 0)))
    (`∀ (`∀ ((＇ 0) ⇒ (＇ 1)))) ≡ true
mlb?-right-unmatched-before-matched-lower-right = refl

------------------------------------------------------------------------
-- Regression cases for rejected variable/star assumptions
------------------------------------------------------------------------

mlb?-rejects-var-star :
  mlb? (＇ 0) ★ ≡ nothing
mlb?-rejects-var-star = refl

mlb?-rejects-var-star-lower-right :
  MlbResultLowerRight? 1 (＇ 0) ★ ≡ false
mlb?-rejects-var-star-lower-right = refl

mlb?-rejects-star-var :
  mlb? ★ (＇ 0) ≡ nothing
mlb?-rejects-star-var = refl

mlb?-rejects-star-var-lower-left :
  MlbResultLowerLeft? 1 ★ (＇ 0) ≡ false
mlb?-rejects-star-var-lower-left = refl

mlb?-rejects-forall-var-star :
  mlb? (`∀ ((＇ 0) ⇒ (＇ 0))) (`∀ ((＇ 0) ⇒ ★)) ≡
  nothing
mlb?-rejects-forall-var-star = refl

mlb?-rejects-forall-var-star-lower-right :
  MlbResultLowerRight? 0 (`∀ ((＇ 0) ⇒ (＇ 0))) (`∀ ((＇ 0) ⇒ ★)) ≡
  false
mlb?-rejects-forall-var-star-lower-right = refl

mlb?-rejects-var-var-and-var-star :
  mlb? ((＇ 0) ⇒ (＇ 0)) ((＇ 0) ⇒ ★) ≡ nothing
mlb?-rejects-var-var-and-var-star = refl

mlb?-rejects-var-star-and-var-var :
  mlb? ((＇ 0) ⇒ (＇ 0)) (★ ⇒ (＇ 0)) ≡ nothing
mlb?-rejects-var-star-and-var-var = refl

mlb?-rejects-var-var-and-star-var :
  mlb? ((＇ 0) ⇒ ★) ((＇ 0) ⇒ (＇ 0)) ≡ nothing
mlb?-rejects-var-var-and-star-var = refl

mlb?-rejects-star-var-and-var-var :
  mlb? (★ ⇒ (＇ 0)) ((＇ 0) ⇒ (＇ 0)) ≡ nothing
mlb?-rejects-star-var-and-var-var = refl

mlb?-rejects-hoisted-unused-forall :
  mlb? (`∀ (★ ⇒ (＇ 0))) (★ ⇒ (`∀ (＇ 0))) ≡ nothing
mlb?-rejects-hoisted-unused-forall = refl

mlb?-rejects-escaping-local-equation :
  mlb? (`∀ (★ ⇒ ((＇ 0) ⇒ (`∀ (＇ 0)))))
       (`∀ (`∀ ((＇ 0) ⇒ ((＇ 1) ⇒ (＇ 0))))) ≡
  nothing
mlb?-rejects-escaping-local-equation = refl

mlb?-rejects-base-mismatch :
  mlb? (‵ `ℕ) (‵ `𝔹) ≡ nothing
mlb?-rejects-base-mismatch = refl

mlb?-rejects-equation-clash-same-left :
  mlb? ((＇ 0) ⇒ (＇ 0)) ((＇ 0) ⇒ (＇ 1)) ≡ nothing
mlb?-rejects-equation-clash-same-left = refl

mlb?-rejects-equation-clash-same-right :
  mlb? ((＇ 0) ⇒ (＇ 1)) ((＇ 0) ⇒ (＇ 0)) ≡ nothing
mlb?-rejects-equation-clash-same-right = refl

mlb?-rejects-forall-equation-clash :
  mlb? (`∀ ((＇ 0) ⇒ (＇ 0))) (`∀ ((＇ 0) ⇒ (＇ 1))) ≡ nothing
mlb?-rejects-forall-equation-clash = refl

mlb?-rejects-crossed-forall-binder-equations :
  mlb? (`∀ (`∀ ((＇ 1) ⇒ (＇ 0)))) (`∀ (`∀ ((＇ 0) ⇒ (＇ 1)))) ≡
  nothing
mlb?-rejects-crossed-forall-binder-equations = refl
