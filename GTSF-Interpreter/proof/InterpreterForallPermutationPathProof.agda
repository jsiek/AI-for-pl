module proof.InterpreterForallPermutationPathProof where

-- File Charter:
--   * Normalizes raw `∀`-permutation evidence into finite oriented paths.
--   * Folds normalized paths with identity and single-exchange operations.
--   * Uses only pure type and permutation metatheory.

open import ForallPermutation using
  ( _≈∀_
  ; ≈∀-refl
  ; ≈∀-sym
  ; ≈∀-trans
  ; ≈∀-⇒
  ; ≈∀-∀
  ; ≈∀-swap
  )
open import Simulation.Polymorphism.InterpreterForallPermutationPathDefinition
open import Types using (Ty; _⇒_; `∀)


exchange-sym :
  ∀ {A B} →
  A ↝∀ B →
  B ↝∀ A
exchange-sym exchange = unexchange
exchange-sym unexchange = exchange
exchange-sym (arrow-left step) = arrow-left (exchange-sym step)
exchange-sym (arrow-right step) = arrow-right (exchange-sym step)
exchange-sym (under-all step) = under-all (exchange-sym step)


path-trans :
  ∀ {A B C} →
  A ≈∀ⁿ B →
  B ≈∀ⁿ C →
  A ≈∀ⁿ C
path-trans [] B≈C = B≈C
path-trans (step ∷ A≈B) B≈C = step ∷ path-trans A≈B B≈C


path-sym :
  ∀ {A B} →
  A ≈∀ⁿ B →
  B ≈∀ⁿ A
path-sym [] = []
path-sym (step ∷ B≈C) =
  path-trans (path-sym B≈C) (exchange-sym step ∷ [])


path-arrow-left :
  ∀ {A A′ B} →
  A ≈∀ⁿ A′ →
  A ⇒ B ≈∀ⁿ A′ ⇒ B
path-arrow-left [] = []
path-arrow-left (step ∷ rest) =
  arrow-left step ∷ path-arrow-left rest


path-arrow-right :
  ∀ {A B B′} →
  B ≈∀ⁿ B′ →
  A ⇒ B ≈∀ⁿ A ⇒ B′
path-arrow-right [] = []
path-arrow-right (step ∷ rest) =
  arrow-right step ∷ path-arrow-right rest


path-all :
  ∀ {A B} →
  A ≈∀ⁿ B →
  `∀ A ≈∀ⁿ `∀ B
path-all [] = []
path-all (step ∷ rest) = under-all step ∷ path-all rest


normalize-forall-permutation-proof :
  ∀ {A B} →
  A ≈∀ B →
  A ≈∀ⁿ B
normalize-forall-permutation-proof ≈∀-refl = []
normalize-forall-permutation-proof (≈∀-sym A≈B) =
  path-sym (normalize-forall-permutation-proof A≈B)
normalize-forall-permutation-proof (≈∀-trans A≈B B≈C) =
  path-trans
    (normalize-forall-permutation-proof A≈B)
    (normalize-forall-permutation-proof B≈C)
normalize-forall-permutation-proof (≈∀-⇒ A≈A′ B≈B′) =
  path-trans
    (path-arrow-left (normalize-forall-permutation-proof A≈A′))
    (path-arrow-right (normalize-forall-permutation-proof B≈B′))
normalize-forall-permutation-proof (≈∀-∀ A≈B) =
  path-all (normalize-forall-permutation-proof A≈B)
normalize-forall-permutation-proof ≈∀-swap = exchange ∷ []


fold-forall-permutation-path-proof :
  (P : Ty → Ty → Set₁) →
  ((A : Ty) → P A A) →
  (∀ {A B C} → A ↝∀ B → P B C → P A C) →
  ∀ {A B} →
  A ≈∀ⁿ B →
  P A B
fold-forall-permutation-path-proof P identity prepend [] = identity _
fold-forall-permutation-path-proof P identity prepend (step ∷ rest) =
  prepend step
    (fold-forall-permutation-path-proof P identity prepend rest)
