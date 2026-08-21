{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.ConversionPivotAlignmentProbe where

-- File Charter:
--   * Checks the computed generator-position gate on the paired conversions
--     used by Example 12's active left path.
--   * Keeps the basic matched and source-only conversion shapes visible.
--   * Records generated both/right cross-position counterexamples rejected by
--     the gate before term-imprecision migration.

open import Data.Fin using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (★; ＇_; ‵_; _⇒_; `ℕ)
open import TyStore using (TyStore; store-empty; store-bind; Z∋)
import Conversion as Conv
open Conv using
  (Conv↑; Conv↓; 〖_,_↑_〗; makeConceal)
import proof.DGG.Examples2 as Ex2
open import proof.DGG.ConversionPivotAlignment


------------------------------------------------------------------------
-- Active Example 12 gates
------------------------------------------------------------------------

example12-Y-arrow-reveal-aligns :
  revealGeneratorPosition Ex2.left-path-source-Y-reveal₃-⊢
    ≡ revealGeneratorPosition Ex2.left-path-target-Y-reveal₃-⊢
example12-Y-arrow-reveal-aligns = refl

example12-Z-arrow-reveal-aligns :
  revealGeneratorPosition Ex2.left-path-source-Z-reveal₃-⊢
    ≡ revealGeneratorPosition Ex2.left-path-target-Z-reveal₃-⊢
example12-Z-arrow-reveal-aligns = refl

example12-Z-seal-aligns :
  concealGeneratorPosition Ex2.left-path-source-Z-seal₄-⊢
    ≡ concealGeneratorPosition Ex2.left-path-target-Z-seal₄-⊢
example12-Z-seal-aligns = refl

example12-Z-unseal-aligns :
  revealGeneratorPosition Ex2.left-path-source-Z-unseal₄-⊢
    ≡ revealGeneratorPosition Ex2.left-path-target-Z-unseal₄-⊢
example12-Z-unseal-aligns = refl

example12-Y-seal-aligns :
  concealGeneratorPosition Ex2.left-path-source-Y-seal₄-⊢
    ≡ concealGeneratorPosition Ex2.left-path-target-Y-seal₄-⊢
example12-Y-seal-aligns = refl

example12-Y-unseal-aligns :
  revealGeneratorPosition Ex2.left-path-source-Y-unseal₄-⊢
    ≡ revealGeneratorPosition Ex2.left-path-target-Y-unseal₄-⊢
example12-Y-unseal-aligns = refl


------------------------------------------------------------------------
-- Basic matched and source-only shapes
------------------------------------------------------------------------

matched-arrow-position :
  revealGeneratorPosition Ex2.left-path-source-Y-reveal₃-⊢
    ≡ generator-⇒-both generator-here generator-here
matched-arrow-position = refl

source-only-arrow-position :
  revealGeneratorPosition Ex2.left-path-source-X-reveal₃-⊢
    ≡ generator-⇒-both generator-here generator-here
source-only-arrow-position = refl

source-only-seal-position :
  concealGeneratorPosition Ex2.left-path-source-X-seal₄-⊢
    ≡ generator-here
source-only-seal-position = refl


------------------------------------------------------------------------
-- Cross-position counterexample
------------------------------------------------------------------------

source-store : TyStore 1
source-store = store-bind store-empty (‵ `ℕ)

target-store : TyStore 1
target-store = store-bind store-empty ★

source-generated-reveal :
  Conv↑ 1 (＇ zero ⇒ ＇ zero) (‵ `ℕ ⇒ ‵ `ℕ)
source-generated-reveal = 〖 zero , ‵ `ℕ ↑ (＇ zero ⇒ ＇ zero) 〗

source-generated-reveal-⊢ :
  source-store Conv.⊢↑[ zero ⦂ ‵ `ℕ ] source-generated-reveal
source-generated-reveal-⊢ =
  Conv.⊢↑-⇒ (Conv.⊢↓-seal (Z∋ refl))
    (Conv.⊢↑-unseal (Z∋ refl))

target-result-reveal :
  Conv↑ 1 (★ ⇒ ＇ zero) (★ ⇒ ★)
target-result-reveal = 〖 zero , ★ ↑ (★ ⇒ ＇ zero) 〗

target-result-reveal-⊢ :
  target-store Conv.⊢↑[ zero ⦂ ★ ] target-result-reveal
target-result-reveal-⊢ =
  Conv.⊢↑-⇒ (Conv.⊢↓-id-star (Z∋ refl))
    (Conv.⊢↑-unseal (Z∋ refl))

source-generated-position :
  revealGeneratorPosition source-generated-reveal-⊢
    ≡ generator-⇒-both generator-here generator-here
source-generated-position = refl

target-result-position :
  revealGeneratorPosition target-result-reveal-⊢
    ≡ generator-⇒-right generator-here
target-result-position = refl

cross-position-rejected :
  revealGeneratorPosition source-generated-reveal-⊢
    ≢ revealGeneratorPosition target-result-reveal-⊢
cross-position-rejected ()

source-generated-conceal :
  Conv↓ 1 (‵ `ℕ ⇒ ‵ `ℕ) (＇ zero ⇒ ＇ zero)
source-generated-conceal =
  makeConceal zero (‵ `ℕ) (＇ zero ⇒ ＇ zero)

source-generated-conceal-⊢ :
  source-store Conv.⊢↓[ zero ⦂ ‵ `ℕ ] source-generated-conceal
source-generated-conceal-⊢ =
  Conv.⊢↓-⇒ (Conv.⊢↑-unseal (Z∋ refl))
    (Conv.⊢↓-seal (Z∋ refl))

target-result-conceal :
  Conv↓ 1 (★ ⇒ ★) (★ ⇒ ＇ zero)
target-result-conceal = makeConceal zero ★ (★ ⇒ ＇ zero)

target-result-conceal-⊢ :
  target-store Conv.⊢↓[ zero ⦂ ★ ] target-result-conceal
target-result-conceal-⊢ =
  Conv.⊢↓-⇒ (Conv.⊢↑-id-star (Z∋ refl))
    (Conv.⊢↓-seal (Z∋ refl))

conceal-cross-position-rejected :
  concealGeneratorPosition source-generated-conceal-⊢
    ≢ concealGeneratorPosition target-result-conceal-⊢
conceal-cross-position-rejected ()
