module proof.NuImprecisionOneStepDef where

-- File Charter:
--   * Defines the complete target-oriented indexed one-step simulation
--     contract used as a major DGG proof dependency.
--   * Contains no implementation and imports only statement-level support.

open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (StoreChange; _—→[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (RuntimeOK)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuImprecisionSimulationResultDef using
  (WeakOneStepIndexedOutcome)


WeakOneStepIndexedSimulationᵀ : Set₁
WeakOneStepIndexedSimulationᵀ =
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  M′ —→[ χ ] N′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p
