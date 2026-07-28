module proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourcePureStepCasesDef where

-- File Charter:
--   * Defines the world-coherent source pure-step outcome boundary.
--   * Partitions pure roots by their four exhaustive outer source shapes.
--   * Keeps ambient-prefix, refined typing, runtime, store, and world
--     premises explicit while retaining narrower leaf capabilities.
--   * Contains no dispatcher, semantic implementation, postulate, or hole.

open import Data.List using ([])

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; Term)
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
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootDef
  using (WorldCoherentSourceApplicationPureRootᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceCastPureRootDef
  using (WorldCoherentSourceCastPureRootᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitivePureRootDef
  using (WorldCoherentSourcePrimitivePureRootᵀ)
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceRuntimeBulletPureRootDef
  using (WorldCoherentSourceRuntimeBulletPureRootᵀ)
open import TermTyping using (_∣_∣_⊢_⦂_)


WorldCoherentSourcePureStepᵀ : Set₁
WorldCoherentSourcePureStepᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M →
  RuntimeOK M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  M —→ L →
  WorldCoherentSourceOneStepOutcome
    {M = M} {M′ = M′} {L = L} {χ = keep} {ρ = ρ⁺} p


record WorldCoherentSourcePureStepCases : Set₁ where
  field
    sourceApplicationPureRootCase :
      WorldCoherentSourceApplicationPureRootᵀ

    sourceRuntimeBulletPureRootCase :
      WorldCoherentSourceRuntimeBulletPureRootᵀ

    sourceCastPureRootCase :
      WorldCoherentSourceCastPureRootᵀ

    sourcePrimitivePureRootCase :
      WorldCoherentSourcePrimitivePureRootᵀ

open WorldCoherentSourcePureStepCases public
