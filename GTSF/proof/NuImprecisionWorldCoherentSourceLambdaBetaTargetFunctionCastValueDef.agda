module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastValueDef
  where

-- File Charter:
--   * Defines target function-cast beta scheduling after its argument is a
--     value.
--   * Isolates the recursive function-cast spine from argument catch-up.
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


WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ : Set₁
WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ =
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
  Value W →
  Value V′ →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V}
    {M′ = (W ⟨ c C.↦ d ⟩) · V′}
    {L = N [ V ]} {χ = keep} {ρ = ρ⁺} pB
