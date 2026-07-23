module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectDef
  where

-- File Charter:
--   * Defines direct scheduling when the target function is an inert
--     function-cast value.
--   * Isolates the target `β-↦` administration from lambda/lambda beta.
--   * Contains no implementation, result wrapper, postulate, hole, or
--     permissive option.

import Coercions as C
open import Data.List using ([])

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
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ : Set₁
WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ =
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
  Value W →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V}
    {M′ = (W ⟨ c C.↦ d ⟩) · R′}
    {L = N [ V ]} {χ = keep} {ρ = ρ⁺} pB
