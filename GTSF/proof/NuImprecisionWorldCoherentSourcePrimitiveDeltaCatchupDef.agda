module
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupDef
  where

-- File Charter:
--   * Defines the general source-delta catch-up capability.
--   * Allows an arbitrary related target rather than only the synchronized
--     primitive redex handled by the delta-root leaf.
--   * Retains the ambient prefix and exact strong source-step result.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([])
open import Data.Nat using (ℕ; _+_)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
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
open import Types using (Ty; TyCtx; `ℕ; ‵_)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourcePrimitiveDeltaCatchupᵀ : Set₁
WorldCoherentSourcePrimitiveDeltaCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {m n : ℕ} {M′ : Term} {B : Ty}
    {p : Φ ∣ Δᴸ ⊢ ‵ `ℕ ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ $ (κℕ m) ⊕[ addℕ ] $ (κℕ n) ⊑ M′
      ⦂ ‵ `ℕ ⊑ B ∶ p →
  WorldCoherentSourceOneStepIndexedResult
    {M = $ (κℕ m) ⊕[ addℕ ] $ (κℕ n)}
    {M′ = M′}
    {L = $ (κℕ (m + n))}
    {A = ‵ `ℕ} {B = B}
    {χ = keep} {ρ = ρ⁺} p
