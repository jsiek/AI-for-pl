module
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletDef
  where

-- File Charter:
--   * Defines source function-cast beta scheduling against a target runtime
--     bullet.
--   * Isolates the reusable application/target-value exclusion from direct
--     application and mechanical target frames.
--   * Contains no implementation, result wrapper, postulate, hole, or
--     permissive option.

import Coercions as C
open import Data.List using ([])
open import Data.Nat using (suc)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; ⇑ᴿᵢ)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; Term; Value; _•; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceFunctionCastBetaTargetBulletᵀ : Set₁
WorldCoherentSourceFunctionCastBetaTargetBulletᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {V W L′ : Term} {c d : C.Coercion} {A B : Ty}
    {p : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive (⇑ᴿᵢ Φ) →
  AssumptionMembershipUnique (⇑ᴿᵢ Φ) →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf (suc Δᴿ) (rightStoreⁱ ρ⁺) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK (L′ •) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ []
    ⊢ (V ⟨ c C.↦ d ⟩) · W ⦂ A →
  suc Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ L′ • ⦂ B →
  ⇑ᴿᵢ Φ ∣ Δᴸ ∣ suc Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ (V ⟨ c C.↦ d ⟩) · W ⊑ L′ • ⦂ A ⊑ B ∶ p →
  Value V →
  Value W →
  WorldCoherentSourceOneStepIndexedResult
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = L′ •}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {χ = keep} {ρ = ρ⁺} p
