module proof.NuImprecisionQuotientArrowComponents where

-- File Charter:
--   * Decomposes forall-permutation equivalence and quotient precision at
--     arrow endpoints.
--   * Isolates this DGG-specific inversion from the broadly imported general
--     forall-permutation properties module.
--   * Contains no postulate, hole, catch-all, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_×_; _,_)
open import ForallPermutation using
  (_≈∀_; _∣_⊢_⊑ᵖ_⊣_; quotientᵖ; ≈∀-refl; ≈∀-sym; ≈∀-trans; ≈∀-⇒)
open import ImprecisionWf using (_↦_)
open import Types using (_⇒_)
open import proof.ForallPermutationProperties using
  (≈∀-arrow-left; ≈∀-arrow-right)


≈∀-arrow-components :
  ∀ {A A′ B B′} →
  A ⇒ B ≈∀ A′ ⇒ B′ →
  (A ≈∀ A′) × (B ≈∀ B′)
≈∀-arrow-components ≈∀-refl =
  ≈∀-refl , ≈∀-refl
≈∀-arrow-components (≈∀-sym equivalence)
    with ≈∀-arrow-components equivalence
≈∀-arrow-components (≈∀-sym equivalence)
    | domain , codomain =
  ≈∀-sym domain , ≈∀-sym codomain
≈∀-arrow-components
    (≈∀-trans left right)
    with ≈∀-arrow-right left
≈∀-arrow-components
    (≈∀-trans left right)
    | C , D , refl
    with ≈∀-arrow-components left
       | ≈∀-arrow-components right
≈∀-arrow-components
    (≈∀-trans left right)
    | C , D , refl
    | A≈C , B≈D
    | C≈A′ , D≈B′ =
  ≈∀-trans A≈C C≈A′ , ≈∀-trans B≈D D≈B′
≈∀-arrow-components (≈∀-⇒ domain codomain) =
  domain , codomain


⊑ᵖ-arrow-components :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′} →
  Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ →
  (Φ ∣ Δᴸ ⊢ A ⊑ᵖ A′ ⊣ Δᴿ) ×
  (Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ)
⊑ᵖ-arrow-components
    (quotientᵖ left middle right)
    with ≈∀-arrow-right left
       | ≈∀-arrow-left right
⊑ᵖ-arrow-components
    (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    with ≈∀-arrow-components left
       | middle
       | ≈∀-arrow-components right
⊑ᵖ-arrow-components
    (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    | A≈C , B≈D
    | domain ↦ codomain
    | C′≈A′ , D′≈B′ =
  quotientᵖ A≈C domain C′≈A′ ,
  quotientᵖ B≈D codomain D′≈B′
