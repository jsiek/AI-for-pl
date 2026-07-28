module
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupProof
  where

-- File Charter:
--   * Normalizes arbitrary forall-permutation evidence to oriented paths.
--   * Gives a generic identity-and-step interpreter for normalized paths.
--   * Reduces representative-inst catch-up to one path-aware capability.
--   * Imports no dequotienting theorem, simulation core, or dispatcher.

open import Agda.Builtin.Equality using (refl)
open import ForallPermutation using (_≈∀_)
open import Types using (Ty)
open import proof.Core.Permutation.ForallPermutationPath using
  ( _↝∀_
  ; _≈∀ⁿ_
  ; element-all
  ; element-arrow-left
  ; element-arrow-right
  ; element-swap
  ; element-unswap
  ; normalize-forall-permutation
  ; path-refl
  ; path-step
  )
open import
  proof.WorldCoherent.Quotient.Core.NuImprecisionWorldCoherentQuotientRepresentativeInstCatchupDef
  using (WorldCoherentQuotientRepresentativeInstCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.InstPath.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathCatchupᵀ)

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
    inert-d′ inert-u′ down widening
    u-shape u′-shape up-square =
  path-catchup
    (normalize-forall-permutation D≈C)
    (normalize-forall-permutation C′≈D′)
    refl refl
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
    u-shape u′-shape up-square
