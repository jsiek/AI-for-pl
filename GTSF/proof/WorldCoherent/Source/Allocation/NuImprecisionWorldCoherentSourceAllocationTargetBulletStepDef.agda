module
  proof.WorldCoherent.Source.Allocation.NuImprecisionWorldCoherentSourceAllocationTargetBulletStepDef
  where

-- File Charter:
--   * Defines exact source allocation across a target runtime-bullet node.
--   * Exposes the existing indexed success result directly, without another
--     result or outcome wrapper.
--   * Contains no implementation, postulate, hole, permissive option, or
--     broad simulation import.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)

open import Coercions using (Coercion)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; ⇑ᴿᵢ)
open import NuReduction using (bind)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; ν; ⇑ᵗᵐ; _•; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; WfTy; `∀; ⇑ᵗ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceAllocationTargetBulletStepᵀ : Set₁
WorldCoherentSourceAllocationTargetBulletStepᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {ρ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {C A B C′ : Ty} {V L′ : Term} {c : Coercion}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ} →
  (h⇑A : WfTy (suc Δᴿ) (⇑ᵗ A)) →
  StoreImpPrefix
    (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ) ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive (⇑ᴿᵢ Φ) →
  AssumptionMembershipUnique (⇑ᴿᵢ Φ) →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf (suc Δᴿ) (rightStoreⁱ ρ⁺) →
  RuntimeOK (ν C V c) →
  RuntimeOK ((⇑ᵗᵐ L′) •) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ ν C V c ⦂ B →
  suc Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ []
    ⊢ (⇑ᵗᵐ L′) • ⦂ C′ →
  Value L′ →
  No• L′ →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ ν C V c ⊑ L′ ⦂ B ⊑ `∀ C′ ∶ q →
  Δᴸ
    ∣ leftStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ)
    ∣ [] ⊢ ν C V c ⦂ B →
  suc Δᴿ
    ∣ rightStoreⁱ (store-right zero (⇑ᵗ A) h⇑A ∷ ρᴿ)
    ∣ [] ⊢ (⇑ᵗᵐ L′) • ⦂ C′ →
  Value V →
  No• V →
  WorldCoherentSourceOneStepIndexedResult
    {M = ν C V c} {M′ = (⇑ᵗᵐ L′) •}
    {L = ((⇑ᵗᵐ V) •) ⟨ c ⟩}
    {χ = bind C} {ρ = ρ⁺} r
