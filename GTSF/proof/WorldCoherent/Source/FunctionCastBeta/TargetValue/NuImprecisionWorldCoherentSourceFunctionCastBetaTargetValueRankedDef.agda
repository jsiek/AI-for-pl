module
  proof.WorldCoherent.Source.FunctionCastBeta.TargetValue.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueRankedDef
  where

-- File Charter:
--   * Defines exact-rank variants of the source function-cast beta terminal
--     with either an arbitrary or value target argument.
--   * Makes the decreasing target function-cast spine explicit only at the
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
  (RuntimeOK; Term; Value; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; _⇒_)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef using
  (targetFunctionCastSpineRank)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceFunctionCastBetaTargetValuesAtᵀ : ℕ → Set₁
WorldCoherentSourceFunctionCastBetaTargetValuesAtᵀ n =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK (L′ · R′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⟨ c C.↦ d ⟩ ⊑ L′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value W →
  (vL′ : Value L′) →
  Value R′ →
  targetFunctionCastSpineRank vL′ ≡ n →
  WorldCoherentSourceOneStepIndexedResult
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = L′ · R′}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {χ = keep} {ρ = ρ} pB


WorldCoherentSourceFunctionCastBetaTargetValueAtᵀ : ℕ → Set₁
WorldCoherentSourceFunctionCastBetaTargetValueAtᵀ n =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK (L′ · R′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⟨ c C.↦ d ⟩ ⊑ L′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value W →
  (vL′ : Value L′) →
  targetFunctionCastSpineRank vL′ ≡ n →
  WorldCoherentSourceOneStepIndexedResult
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = L′ · R′}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {χ = keep} {ρ = ρ⁺} pB


WorldCoherentSourceFunctionCastBetaTargetFunctionCastValuesAtᵀ :
  ℕ → Set₁
WorldCoherentSourceFunctionCastBetaTargetFunctionCastValuesAtᵀ n =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d e f : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK ((L′ ⟨ e C.↦ f ⟩) · R′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⟨ c C.↦ d ⟩ ⊑ L′ ⟨ e C.↦ f ⟩
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value W →
  (vL′ : Value L′) →
  Value R′ →
  suc (targetFunctionCastSpineRank vL′) ≡ n →
  WorldCoherentSourceOneStepIndexedResult
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = (L′ ⟨ e C.↦ f ⟩) · R′}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {χ = keep} {ρ = ρ} pB
