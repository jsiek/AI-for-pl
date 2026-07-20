module proof.NuImprecisionWorldCoherentOneStepDef where

-- File Charter:
--   * Defines the world-coherent target-oriented indexed one-step simulation
--     contract used by the backward terminal proof.
--   * Requires coherence of the input world and returns it for every related
--     successor world.
--   * Contains no implementation and imports only statement-level support.

open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (StoreChange; _—→[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (RuntimeOK)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentWeakOneStepIndexedOutcome)


WorldCoherentWeakOneStepIndexedSimulationᵀ : Set₁
WorldCoherentWeakOneStepIndexedSimulationᵀ =
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  M′ —→[ χ ] N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p
