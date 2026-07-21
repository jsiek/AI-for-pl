module proof.NuImprecisionWorldCoherentSourceUnsealCatchupDef where

-- File Charter:
--   * Defines coherent catch-up through one active source unseal.
--   * Uses the final coherence and source-store well-formedness carried by
--     the already-computed inner catch-up result.
--   * Contains no implementation or recursive dispatcher dependency.

open import Coercions using (ModeEnv; unseal)
open import Conversion using (RevealConversion)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ)
open import NuTerms using
  (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Types using (Ty; TyCtx; TyVar; ＇_)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentSourceUnsealCatchupᵀ : Set₁
WorldCoherentSourceUnsealCatchupᵀ =
  ∀ {Φ} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ : Term} {B′ X : Ty}
    {μ : ModeEnv} {α : TyVar}
    {p : Φ ∣ Δᴸ ⊢ ＇ α ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X
    (unseal α X) (＇ α) X →
  Value V′ →
  No• V′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ X ⊑ B′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ unseal α X ⟩}
    {V′ = V′} {ρ = ρ⁺} q
