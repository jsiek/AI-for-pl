module proof.NuImprecisionWorldCoherentValueCatchupDef where

-- File Charter:
--   * Defines the world-coherent already-terminal target-value catch-up
--     contract used by the backward terminal proof.
--   * Requires coherence of the input world and exposes coherence of the
--     final catch-up world for subsequent composition.
--   * Contains no implementation and imports only statement-level support.

open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; RuntimeOK; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentLeftValueCatchupᵀ : Set₁
WorldCoherentLeftValueCatchupᵀ =
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  RuntimeOK M →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V′ ⦂ A ⊑ B ∶ p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p
