{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionOneStepTargetCastFrames where

-- File Charter:
--   * Freezes the three outcome-level target-cast frames needed by the
--     indexed one-step dispatcher.
--   * Each wrapper consumes an already-computed inner indexed outcome and
--     frames only a target ξ-⟨⟩ step; root cast reductions are outside its
--     scope.
--   * The target coercion receives the inner step's store change, while the
--     source term, store imprecision, and store-change index stay unchanged.
--   * Contains exactly the three intended leaf-proof holes.

open import Coercions using (id-onlyᵈ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using (applyCoercion)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (_⟨_⟩)
open import TermTyping using (CastMode; SealModeStore★)
open import proof.NuImprecisionSimulationCore using
  (WeakOneStepIndexedOutcome)


weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-narrow-cast-indexed-frame-outcomeᵀ = {!!}


weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-widen-cast-indexed-frame-outcomeᵀ = {!!}


weak-one-step-target-widen-id-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-widen-id-cast-indexed-frame-outcomeᵀ = {!!}
