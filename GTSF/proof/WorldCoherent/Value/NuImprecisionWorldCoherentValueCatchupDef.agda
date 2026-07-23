module proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef where

-- File Charter:
--   * Defines the world-coherent already-terminal target-value catch-up
--     contract used by the backward terminal proof.
--   * Requires world coherence, context exclusivity, and left-store
--     well-formedness, and exposes all three at the final catch-up world.
--   * Contains no implementation and imports only statement-level support.

open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentLeftValueCatchupᵀ : Set₁
WorldCoherentLeftValueCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK M →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V′ ⦂ A ⊑ B ∶ p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p
