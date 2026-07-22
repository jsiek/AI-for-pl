module proof.NuImprecisionWorldCoherentSourcePrimitiveRightStepDef where

-- File Charter:
--   * Defines the world-coherent source primitive-right frame capability.
--   * Keeps the value, framed store change, runtime, typing, and indexed
--     simulation outcome explicit at this semantic boundary.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, or broad simulation import.

open import Data.List using ([])

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (Shiftable; StoreChange; applyTerm; _—→[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (RuntimeOK; Term; Value; _⊕[_]_)
open import Primitives using (Prim)
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
open import proof.NuImprecisionWorldCoherentSourceOneStepOutcomeDef using
  (WorldCoherentSourceOneStepOutcome)
open import TermTyping using (_∣_∣_⊢_⦂_)


WorldCoherentSourcePrimitiveRightStepᵀ : Set₁
WorldCoherentSourcePrimitiveRightStepᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {χ : StoreChange} {L M M₁ M′ : Term} {op : Prim}
    {A B : Ty} {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (L ⊕[ op ] M) →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ L ⊕[ op ] M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ L ⊕[ op ] M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Value L →
  Shiftable χ L →
  M —→[ χ ] M₁ →
  WorldCoherentSourceOneStepOutcome
    {M = L ⊕[ op ] M} {M′ = M′}
    {L = applyTerm χ L ⊕[ op ] M₁}
    {χ = χ} {ρ = ρ⁺} p
