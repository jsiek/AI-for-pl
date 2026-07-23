module proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPrefixDef where

-- File Charter:
--   * Defines the ambient-prefix induction boundary for source one-step
--     simulation with an explicit source-blame alternative.
--   * Separates the smaller relational-store witness from the larger physical
--     store used by reduction, typing, and preservation.
--   * Returns the full recursive result needed by evaluation-context cases.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (StoreChange; _—→[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (RuntimeOK)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef using
  (WorldCoherentSourceOneStepOutcome)
open import TermTyping using (_∣_∣_⊢_⦂_)


WorldCoherentSourceOneStepPrefixᵀ : Set₁
WorldCoherentSourceOneStepPrefixᵀ =
  ∀ {Φ Δᴸ Δᴿ M M′ L A B}
    {χ : StoreChange}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  M —→[ χ ] L →
  WorldCoherentSourceOneStepOutcome
    {M = M} {M′ = M′} {L = L} {χ = χ} {ρ = ρ⁺} p
