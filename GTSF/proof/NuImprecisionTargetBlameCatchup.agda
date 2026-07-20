{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionTargetBlameCatchup where

-- File Charter:
--   * Owns source catch-up when a related target is already blame.
--   * Exposes the exact base lemma required by backward target-blame terminal
--     trace induction.
--   * The statement is frozen and checked; the structural proof is the active
--     boundary.

open import Data.List using ([])
open import Data.Product using (∃-syntax)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (_—↠[_]_)
open import NuTermImprecision using
  (StoreImp)
open import NuTerms using (RuntimeOK; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)


left-catchup-target-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ M A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  RuntimeOK M →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ blame ⦂ A ⊑ B ∶ p →
  ∃[ χs ] (M —↠[ χs ] blame)
left-catchup-target-blameᵀ = {!!}
