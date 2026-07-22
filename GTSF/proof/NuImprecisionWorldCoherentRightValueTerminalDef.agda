module proof.NuImprecisionWorldCoherentRightValueTerminalDef where

-- File Charter:
--   * Defines the zero-step terminal base for recursive right-value catch-up.
--   * Lifts an already-related pair of values from a relational-store prefix
--     into the coherent ambient world and returns the full strong result.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (No•; Value)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightValueTerminalᵀ : Set₁
WorldCoherentRightValueTerminalᵀ =
  ∀ {Φ Δᴸ Δᴿ V V′ A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = V′} {ρ = ρ⁺} p
