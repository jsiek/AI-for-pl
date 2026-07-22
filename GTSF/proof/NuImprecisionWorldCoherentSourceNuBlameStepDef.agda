module proof.NuImprecisionWorldCoherentSourceNuBlameStepDef where

-- File Charter:
--   * Defines the world-coherent source `ν`-blame step capability.
--   * Keeps the enclosing binder, runtime, typing, store/world premises, and
--     indexed blame result explicit at this semantic boundary.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, or broad simulation import.

open import Data.List using ([])

open import Coercions using (Coercion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (RuntimeOK; Term; blame; ν)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import TermTyping using (_∣_∣_⊢_⦂_)


WorldCoherentSourceNuBlameStepᵀ : Set₁
WorldCoherentSourceNuBlameStepᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {C : Ty} {c : Coercion} {M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (ν C blame c) →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ ν C blame c ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ ν C blame c ⊑ M′ ⦂ A ⊑ B ∶ p →
  WorldCoherentSourceOneStepIndexedResult
    {M = ν C blame c} {M′ = M′} {L = blame}
    {χ = keep} {ρ = ρ⁺} p
