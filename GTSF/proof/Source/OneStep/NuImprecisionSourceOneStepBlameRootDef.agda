module proof.Source.OneStep.NuImprecisionSourceOneStepBlameRootDef where

-- File Charter:
--   * Defines the reusable keep-step source-to-blame result used by every
--     pure blame root and by the `ν` blame frame.
--   * Keeps the ambient-prefix and strong exact source-step result visible.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  ( RuntimeOK
  ; blame
  )
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
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import TermTyping using (_∣_∣_⊢_⦂_)


WorldCoherentSourceKeepBlameRootᵀ : Set₁
WorldCoherentSourceKeepBlameRootᵀ =
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
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
  M —→[ keep ] blame →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = blame}
    {χ = keep} {ρ = ρ⁺} p
