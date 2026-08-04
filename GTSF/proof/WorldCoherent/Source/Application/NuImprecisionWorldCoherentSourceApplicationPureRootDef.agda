module
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootDef
  where

-- File Charter:
--   * Defines the world-coherent source application-root outcome capability.
--   * Covers every pure root whose source is an application of a value.
--   * Allows function-cast beta to report either a related continuation or
--     source blame while keeping the full ambient-prefix boundary explicit.
--   * Contains no dispatcher, implementation, postulate, hole, or option.

open import Data.List using ([])

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; Term; _·_)
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
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef
  using
  (WorldCoherentSourceOneStepOutcome)
open import TermTyping using (_∣_∣_⊢_⦂_)


WorldCoherentSourceApplicationPureRootᵀ : Set₁
WorldCoherentSourceApplicationPureRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {F V M′ L : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (F · V) →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ F · V ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ F · V ⊑ M′ ⦂ A ⊑ B ∶ p →
  F · V —→ L →
  WorldCoherentSourceOneStepOutcome
    {M = F · V} {M′ = M′} {L = L}
    {χ = keep} {ρ = ρ⁺} p
