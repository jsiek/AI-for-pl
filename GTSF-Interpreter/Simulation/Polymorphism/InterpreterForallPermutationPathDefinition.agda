module Simulation.Polymorphism.InterpreterForallPermutationPathDefinition where

-- File Charter:
--   * Defines oriented adjacent-`∀` exchanges and finite exchange paths.
--   * Gives active quotient simulation a structurally recursive route index.
--   * Contains no interpreter, reduction, or simulation theorem.

open import ForallPermutation using (swap01ᵗ)
open import Types using (Ty; renameᵗ; _⇒_; `∀)


infix 4 _↝∀_
data _↝∀_ : Ty → Ty → Set where
  exchange : ∀ {A} →
    `∀ (`∀ A) ↝∀ `∀ (`∀ (renameᵗ swap01ᵗ A))

  unexchange : ∀ {A} →
    `∀ (`∀ (renameᵗ swap01ᵗ A)) ↝∀ `∀ (`∀ A)

  arrow-left : ∀ {A A′ B} →
    A ↝∀ A′ →
    A ⇒ B ↝∀ A′ ⇒ B

  arrow-right : ∀ {A B B′} →
    B ↝∀ B′ →
    A ⇒ B ↝∀ A ⇒ B′

  under-all : ∀ {A B} →
    A ↝∀ B →
    `∀ A ↝∀ `∀ B


infix 4 _≈∀ⁿ_
data _≈∀ⁿ_ : Ty → Ty → Set where
  [] : ∀ {A} →
    A ≈∀ⁿ A

  _∷_ : ∀ {A B C} →
    A ↝∀ B →
    B ≈∀ⁿ C →
    A ≈∀ⁿ C
