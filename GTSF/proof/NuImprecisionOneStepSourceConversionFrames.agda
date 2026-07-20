{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionOneStepSourceConversionFrames where

-- File Charter:
--   * Freezes the two outcome-level source-conversion frames needed by the
--     indexed one-step dispatcher.
--   * Each wrapper consumes an already-computed inner indexed outcome and
--     leaves the target term, target change, and store imprecision unchanged.
--   * Reveal/conceal provenance supplies the conversion evidence transported
--     across the source catch-up trace.
--   * Contains exactly the two intended leaf-proof holes.

open import Conversion using (ConcealConversion; RevealConversion)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (_⟨_⟩)
open import proof.NuImprecisionSimulationCore using
  (WeakOneStepIndexedOutcome)


weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B B′ c μ α X χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = M′} {χ = χ} {ρ = ρ} q
weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ = {!!}


weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B B′ c μ α X χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = M′} {χ = χ} {ρ = ρ} q
weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ = {!!}
