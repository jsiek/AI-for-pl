module proof.Core.Permutation.ForallPermutationPath where

-- File Charter:
--   * Defines oriented contextual adjacent `∀` swaps and their finite paths.
--   * Normalizes proof-relevant `ForallPermutation._≈∀_` derivations to
--     finite paths.
--   * Provides generic path symmetry, composition, and contextual lifting.
--   * Contains no term relation, reduction, world coherence, or simulation.

open import ForallPermutation using
  ( _≈∀_
  ; ≈∀-refl
  ; ≈∀-sym
  ; ≈∀-trans
  ; ≈∀-⇒
  ; ≈∀-∀
  ; ≈∀-swap
  ; swap01ᵗ
  )
open import Types using (Ty; renameᵗ; _⇒_; `∀)


infix 4 _↝∀_
data _↝∀_ : Ty → Ty → Set where
  element-swap : ∀ {A} →
    `∀ (`∀ A) ↝∀ `∀ (`∀ (renameᵗ swap01ᵗ A))

  element-unswap : ∀ {A} →
    `∀ (`∀ (renameᵗ swap01ᵗ A)) ↝∀ `∀ (`∀ A)

  element-arrow-left : ∀ {A A′ B} →
    A ↝∀ A′ →
    A ⇒ B ↝∀ A′ ⇒ B

  element-arrow-right : ∀ {A B B′} →
    B ↝∀ B′ →
    A ⇒ B ↝∀ A ⇒ B′

  element-all : ∀ {A B} →
    A ↝∀ B →
    `∀ A ↝∀ `∀ B


infix 4 _≈∀ⁿ_
data _≈∀ⁿ_ : Ty → Ty → Set where
  path-refl : ∀ {A} →
    A ≈∀ⁿ A

  path-step : ∀ {A B C} →
    A ↝∀ B →
    B ≈∀ⁿ C →
    A ≈∀ⁿ C


elementary-forall-permutation-sym :
  ∀ {A B} →
  A ↝∀ B →
  B ↝∀ A
elementary-forall-permutation-sym element-swap = element-unswap
elementary-forall-permutation-sym element-unswap = element-swap
elementary-forall-permutation-sym
    (element-arrow-left step) =
  element-arrow-left (elementary-forall-permutation-sym step)
elementary-forall-permutation-sym
    (element-arrow-right step) =
  element-arrow-right (elementary-forall-permutation-sym step)
elementary-forall-permutation-sym (element-all step) =
  element-all (elementary-forall-permutation-sym step)


forall-permutation-path-trans :
  ∀ {A B C} →
  A ≈∀ⁿ B →
  B ≈∀ⁿ C →
  A ≈∀ⁿ C
forall-permutation-path-trans path-refl B≈C = B≈C
forall-permutation-path-trans (path-step step A≈B) B≈C =
  path-step step (forall-permutation-path-trans A≈B B≈C)


forall-permutation-path-sym :
  ∀ {A B} →
  A ≈∀ⁿ B →
  B ≈∀ⁿ A
forall-permutation-path-sym path-refl = path-refl
forall-permutation-path-sym (path-step step B≈C) =
  forall-permutation-path-trans
    (forall-permutation-path-sym B≈C)
    (path-step (elementary-forall-permutation-sym step) path-refl)


forall-permutation-path-arrow-left :
  ∀ {A A′ B} →
  A ≈∀ⁿ A′ →
  A ⇒ B ≈∀ⁿ A′ ⇒ B
forall-permutation-path-arrow-left path-refl = path-refl
forall-permutation-path-arrow-left (path-step step rest) =
  path-step (element-arrow-left step)
    (forall-permutation-path-arrow-left rest)


forall-permutation-path-arrow-right :
  ∀ {A B B′} →
  B ≈∀ⁿ B′ →
  A ⇒ B ≈∀ⁿ A ⇒ B′
forall-permutation-path-arrow-right path-refl = path-refl
forall-permutation-path-arrow-right (path-step step rest) =
  path-step (element-arrow-right step)
    (forall-permutation-path-arrow-right rest)


forall-permutation-path-all :
  ∀ {A B} →
  A ≈∀ⁿ B →
  `∀ A ≈∀ⁿ `∀ B
forall-permutation-path-all path-refl = path-refl
forall-permutation-path-all (path-step step rest) =
  path-step (element-all step)
    (forall-permutation-path-all rest)


normalize-forall-permutation :
  ∀ {A B} →
  A ≈∀ B →
  A ≈∀ⁿ B
normalize-forall-permutation ≈∀-refl = path-refl
normalize-forall-permutation (≈∀-sym A≈B) =
  forall-permutation-path-sym (normalize-forall-permutation A≈B)
normalize-forall-permutation (≈∀-trans A≈B B≈C) =
  forall-permutation-path-trans
    (normalize-forall-permutation A≈B)
    (normalize-forall-permutation B≈C)
normalize-forall-permutation (≈∀-⇒ A≈A′ B≈B′) =
  forall-permutation-path-trans
    (forall-permutation-path-arrow-left
      (normalize-forall-permutation A≈A′))
    (forall-permutation-path-arrow-right
      (normalize-forall-permutation B≈B′))
normalize-forall-permutation (≈∀-∀ A≈B) =
  forall-permutation-path-all (normalize-forall-permutation A≈B)
normalize-forall-permutation ≈∀-swap =
  path-step element-swap path-refl
