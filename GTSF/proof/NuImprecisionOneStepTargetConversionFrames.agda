{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionOneStepTargetConversionFrames where

-- File Charter:
--   * Freezes the two outcome-level target-conversion frames needed by the
--     indexed one-step dispatcher.
--   * Each wrapper consumes an already-computed inner indexed outcome and
--     lifts only the target reduct through the ξ-⟨⟩ frame.
--   * The source term, store imprecision, and initial store change are
--     unchanged; the target coercion is transformed by that initial change.
--   * Excludes root conversion reductions and contains exactly two proof
--     holes, one for reveal and one for conceal.

open import Conversion using (ConcealConversion; RevealConversion)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (applyCoercion)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (_⟨_⟩)
open import proof.NuImprecisionSimulationCore using
  (WeakOneStepIndexedOutcome)


weak-one-step-target-reveal-conversion-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ β X′ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-reveal-conversion-indexed-frame-outcomeᵀ
    c′↑ inner q = {!!}


weak-one-step-target-conceal-conversion-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ β X′ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-conceal-conversion-indexed-frame-outcomeᵀ
    c′↓ inner q = {!!}
