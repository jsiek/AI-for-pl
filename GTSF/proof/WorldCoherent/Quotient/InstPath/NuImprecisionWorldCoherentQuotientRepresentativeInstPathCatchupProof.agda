module
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupProof
  where

-- File Charter:
--   * Normalizes arbitrary forall-permutation evidence to oriented paths.
--   * Gives a generic identity-and-step interpreter for normalized paths.
--   * Reduces representative-inst catch-up to one path-aware capability.
--   * Imports no dequotienting theorem, simulation core, or dispatcher.

open import ForallPermutation using
  ( _≈∀_
  ; ≈∀-refl
  ; ≈∀-sym
  ; ≈∀-trans
  ; ≈∀-⇒
  ; ≈∀-∀
  ; ≈∀-swap
  )
open import Types using (Ty; _⇒_; `∀)
open import
  proof.WorldCoherent.Quotient.Core.NuImprecisionWorldCoherentQuotientRepresentativeInstCatchupDef
  using (WorldCoherentQuotientRepresentativeInstCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef
  using
  ( WorldCoherentQuotientRepresentativeInstPathCatchupᵀ
  ; _↝∀_
  ; _≈∀ⁿ_
  ; element-all
  ; element-arrow-left
  ; element-arrow-right
  ; element-swap
  ; element-unswap
  ; path-refl
  ; path-step
  )


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

interpret-forall-permutation-path :
  (P : Ty → Ty → Set₁) →
  ((A : Ty) → P A A) →
  (∀ {A B C} → A ↝∀ B → P B C → P A C) →
  ∀ {A B} → A ≈∀ⁿ B → P A B
interpret-forall-permutation-path P identity prepend path-refl =
  identity _
interpret-forall-permutation-path P identity prepend
    (path-step step rest) =
  prepend step
    (interpret-forall-permutation-path P identity prepend rest)

interpret-forall-permutation :
  (P : Ty → Ty → Set₁) →
  ((A : Ty) → P A A) →
  (∀ {A B C} → A ↝∀ B → P B C → P A C) →
  ∀ {A B} → A ≈∀ B → P A B
interpret-forall-permutation P identity prepend A≈B =
  interpret-forall-permutation-path P identity prepend
    (normalize-forall-permutation A≈B)

world-coherent-quotient-representative-inst-path-catchup-proofᵀ :
  WorldCoherentQuotientRepresentativeInstPathCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstCatchupᵀ
world-coherent-quotient-representative-inst-path-catchup-proofᵀ
    path-catchup {D≈C = D≈C} {C′≈D′ = C′≈D′}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening =
  path-catchup
    (normalize-forall-permutation D≈C)
    (normalize-forall-permutation C′≈D′)
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
