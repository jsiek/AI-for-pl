module proof.NuImprecisionRightBinderContextLiftProof where

-- File Charter:
--   * Constructs the canonical target-only lift of a relational term context.
--   * Supplies the context witness paired with target-only store-prefix
--     lifting when reconstructing right `ν` roots after substitution.
--   * Contains no term relation, postulate, hole, or permissive option.

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; ∃-syntax)

open import ImprecisionWf using (⇑ᴿᵢ)
open import NuTermImprecision using
  ( CtxImp
  ; LiftRightCtxⁱ
  ; ctx-imp
  ; lift-right-ctx-[]
  ; lift-right-ctx-∷
  )
open import proof.MaximalLowerBoundsWf using
  (⊑-target-lift-rightᵢ)
open import Types using (⇑ᵗ)


lift-right-ctx-result :
  ∀ {Φ Δᴸ Δᴿ} (γ : CtxImp Φ Δᴸ Δᴿ) →
  ∃[ γ′ ] LiftRightCtxⁱ (⇑ᴿᵢ Φ) γ γ′
lift-right-ctx-result [] = [] , lift-right-ctx-[]
lift-right-ctx-result (ctx-imp A B p ∷ γ)
    with lift-right-ctx-result γ
lift-right-ctx-result (ctx-imp A B p ∷ γ) | γ′ , liftγ =
  ctx-imp A (⇑ᵗ B) (⊑-target-lift-rightᵢ p) ∷ γ′ ,
  lift-right-ctx-∷ liftγ
