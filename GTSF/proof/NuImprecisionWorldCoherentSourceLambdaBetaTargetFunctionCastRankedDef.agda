module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastRankedDef
  where

-- File Charter:
--   * Defines exact-rank variants of direct and value-argument target
--     function-cast scheduling.
--   * Makes the decreasing function-cast spine explicit only at the private
--     recursive assembly boundary.
--   * Contains no implementation, result wrapper, postulate, hole, or
--     permissive option.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (ℕ; suc)

open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; Term; Value; ƛ_; _·_; _⟨_⟩; _[_])
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; _⇒_)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionTargetFunctionCastSpineMeasureDef using
  (targetFunctionCastSpineRank)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ : ℕ → Set₁
WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ n =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V W R′ : Term} {c d : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((ƛ N) · V) →
  RuntimeOK ((W ⟨ c C.↦ d ⟩) · R′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ ƛ N ⊑ W ⟨ c C.↦ d ⟩
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  (vW : Value W) →
  suc (targetFunctionCastSpineRank vW) ≡ n →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V}
    {M′ = (W ⟨ c C.↦ d ⟩) · R′}
    {L = N [ V ]} {χ = keep} {ρ = ρ⁺} pB


WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ : ℕ → Set₁
WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ n =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V W V′ : Term} {c d : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((ƛ N) · V) →
  RuntimeOK ((W ⟨ c C.↦ d ⟩) · V′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ ƛ N ⊑ W ⟨ c C.↦ d ⟩
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  (vW : Value W) →
  Value V′ →
  suc (targetFunctionCastSpineRank vW) ≡ n →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V}
    {M′ = (W ⟨ c C.↦ d ⟩) · V′}
    {L = N [ V ]} {χ = keep} {ρ = ρ⁺} pB
