module proof.NuImprecisionSourceOneStepDeltaRootDef where

-- File Charter:
--   * Defines the synchronized natural-addition root used by the source
--     primitive pure-step family.
--   * Keeps the ambient relational-store prefix and final world invariants
--     explicit while fixing the exact source and target delta reductions.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.Nat using (ℕ; _+_)

open import ImprecisionWf using (ImpCtx; idι)
open import NuReduction using (keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using ($; _⊕[_]_)
open import Primitives using (addℕ; κℕ)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Types using (TyCtx; `ℕ; ‵_)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceDeltaRootᵀ : Set₁
WorldCoherentSourceDeltaRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {m n : ℕ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  WorldCoherentSourceOneStepIndexedResult
    {M = $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)}
    {M′ = $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)}
    {L = $ (κℕ (m + n))}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = keep} {ρ = ρ⁺} idι
