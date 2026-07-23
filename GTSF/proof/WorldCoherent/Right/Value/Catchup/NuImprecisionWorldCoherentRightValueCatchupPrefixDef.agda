module proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef where

-- File Charter:
--   * Defines the ambient-prefix induction boundary for right-value catch-up.
--   * Relates terms through a store prefix while running target reduction in
--     the larger coherent ambient store.
--   * Returns the full recursive result rather than the terminal DGG package.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Value)
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
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightValueCatchupPrefixᵀ : Set₁
WorldCoherentRightValueCatchupPrefixᵀ =
  ∀ {Φ Δᴸ Δᴿ V M′ A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M′ →
  Value V →
  No• V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p
