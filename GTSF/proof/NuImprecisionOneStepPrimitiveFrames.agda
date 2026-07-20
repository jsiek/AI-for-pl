{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionOneStepPrimitiveFrames where

-- File Charter:
--   * Freezes the two outcome-level primitive evaluation-context frames
--     needed by the indexed one-step dispatcher.
--   * Each wrapper consumes an already-computed inner indexed outcome, so
--     recursion remains visible in the dispatcher.
--   * Covers only the left-operand and right-operand frames for addition;
--     primitive delta, scheduling boundaries, and root blame live elsewhere.
--   * Contains exactly the two intended leaf-proof holes.

open import Data.List using ([])
open import ImprecisionWf using (_∣_⊢_⊑_⊣_; idι)
open import NuReduction using (applyTerm)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; Value; _⊕[_]_)
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (`ℕ; ‵_)
open import proof.NuImprecisionSimulationCore using
  (WeakOneStepIndexedOutcome)


weak-one-step-⊕₁-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L₁′ M M′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WeakOneStepIndexedOutcome
    {M = L} {N′ = L₁′} {χ = χ} {ρ = ρ} idι →
  WeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = L₁′ ⊕[ addℕ ] applyTerm χ M′}
    {χ = χ} {ρ = ρ} idι
weak-one-step-⊕₁-indexed-frame-outcomeᵀ = {!!}


weak-one-step-⊕₂-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L L′ M M₁′ χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  No• L →
  Value L′ →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = M₁′} {χ = χ} {ρ = ρ} idι →
  WeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = applyTerm χ L′ ⊕[ addℕ ] M₁′}
    {χ = χ} {ρ = ρ} idι
weak-one-step-⊕₂-indexed-frame-outcomeᵀ = {!!}
