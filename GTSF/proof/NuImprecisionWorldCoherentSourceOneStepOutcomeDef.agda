module
  proof.NuImprecisionWorldCoherentSourceOneStepOutcomeDef
  where

-- File Charter:
--   * Defines the recursive source one-step outcome used by forward DGG.
--   * Keeps the exact continuing result separate from source blame reached
--     after the distinguished step and any enclosing-frame propagation.
--   * Contains no implementation, postulate, hole, or permissive option.

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (StoreChange; _—↠[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (blame)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


data WorldCoherentSourceOneStepOutcome
    {Φ Δᴸ Δᴿ M M′ L A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  source-step-outcome-related :
    WorldCoherentSourceOneStepIndexedResult
      {M = M} {M′ = M′} {L = L} {χ = χ} {ρ = ρ} p →
    WorldCoherentSourceOneStepOutcome p

  source-step-outcome-source-blame : ∀ {χs} →
    M —↠[ χs ] blame →
    WorldCoherentSourceOneStepOutcome p
