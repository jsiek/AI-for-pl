module proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceNuFrameStepDef where

-- File Charter:
--   * Defines the world-coherent source `ν`-frame step capability.
--   * Keeps type/coercion transport under the binder, runtime, typing, and
--     indexed simulation outcome explicit at this semantic boundary.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, or broad simulation import.

open import Data.List using ([])

open import Coercions using (Coercion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChange
  ; applyCoercionUnderTyBinder
  ; applyTy
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (RuntimeOK; Term; ν)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef using
  (WorldCoherentSourceOneStepOutcome)
open import TermTyping using (_∣_∣_⊢_⦂_)


WorldCoherentSourceNuFrameStepᵀ : Set₁
WorldCoherentSourceNuFrameStepᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {χ : StoreChange} {C : Ty} {L L′ M′ : Term}
    {c : Coercion} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (ν C L c) →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ ν C L c ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ ν C L c ⊑ M′ ⦂ A ⊑ B ∶ p →
  L —→[ χ ] L′ →
  WorldCoherentSourceOneStepOutcome
    {M = ν C L c} {M′ = M′}
    {L = ν (applyTy χ C) L′
      (applyCoercionUnderTyBinder χ c)}
    {χ = χ} {ρ = ρ⁺} p
