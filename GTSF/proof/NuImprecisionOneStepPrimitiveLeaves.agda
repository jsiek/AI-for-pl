{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionOneStepPrimitiveLeaves where

-- File Charter:
--   * Freezes the runtime views and non-crossed primitive leaves needed by
--     the indexed one-step dispatcher.
--   * Covers Nat-value inversion and the primitive blame roots that do not
--     require transporting an operand across the other operand's catch-up.
--   * Excludes delta and crossed ξ schedules.
--   * Contains exactly five intended leaf-proof holes.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)

open import ImprecisionWf using (idι)
open import NuReduction using (keep; _—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Value
  ; $
  ; blame
  ; _⊕[_]_
  )
open import Primitives using (addℕ; κℕ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (`ℕ; ‵_)
open import proof.NuImprecisionSimulationCore using
  (WeakOneStepIndexedOutcome)


runtime-⊕₁-viewᵀ :
  ∀ {L L′ L₁′ M M′ χ} →
  RuntimeOK (L ⊕[ addℕ ] M) →
  RuntimeOK (L′ ⊕[ addℕ ] M′) →
  L′ —→[ χ ] L₁′ →
  (No• M × No• M′) ⊎
  (Value L × No• L × RuntimeOK M × No• M′)
runtime-⊕₁-viewᵀ = {!!}


runtime-⊕₂-viewᵀ :
  ∀ {L L′ M M′} →
  RuntimeOK (L ⊕[ addℕ ] M) →
  RuntimeOK (L′ ⊕[ addℕ ] M′) →
  Value L′ →
  (Value L × No• L × RuntimeOK M × No• L′) ⊎
  (RuntimeOK L × No• M × No• L′)
runtime-⊕₂-viewᵀ = {!!}


related-nat-value-target-constantᵀ :
  ∀ {Φ Δᴸ Δᴿ V n}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ $ (κℕ n) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  V ≡ $ (κℕ n)
related-nat-value-target-constantᵀ = {!!}


weak-one-step-⊕-left-blame-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L M}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RuntimeOK (L ⊕[ addℕ ] M) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ blame ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = blame} {χ = keep} {ρ = ρ} idι
weak-one-step-⊕-left-blame-indexed-outcomeᵀ = {!!}


weak-one-step-⊕-right-blame-right-first-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L M}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Value L →
  No• L →
  RuntimeOK M →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ blame ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M}
    {N′ = blame} {χ = keep} {ρ = ρ} idι
weak-one-step-⊕-right-blame-right-first-indexed-outcomeᵀ = {!!}
