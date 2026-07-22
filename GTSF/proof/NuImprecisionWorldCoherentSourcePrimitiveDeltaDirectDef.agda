module
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaDirectDef
  where

-- File Charter:
--   * Defines the direct two-operand source-delta scheduling boundary.
--   * Covers an unframed target primitive whose operands are each related to
--     the corresponding source natural constant.
--   * Contains no scheduling proof, target-frame recursion, hole, or option.

open import Data.List using ([])
open import Data.Nat using (ℕ; _+_)

open import ImprecisionWf using (ImpCtx; idι)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (RuntimeOK; Term; $; _⊕[_]_)
open import Primitives using (addℕ; κℕ)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (TyCtx; `ℕ; ‵_)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourcePrimitiveDeltaDirectᵀ : Set₁
WorldCoherentSourcePrimitiveDeltaDirectᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {m n : ℕ} {L′ R′ : Term} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (L′ ⊕[ addℕ ] R′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ $ (κℕ m) ⊑ L′
      ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ $ (κℕ n) ⊑ R′
      ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WorldCoherentSourceOneStepIndexedResult
    {M = $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)}
    {M′ = L′ ⊕[ addℕ ] R′}
    {L = $ (κℕ (m + n))}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = keep} {ρ = ρ⁺} idι
