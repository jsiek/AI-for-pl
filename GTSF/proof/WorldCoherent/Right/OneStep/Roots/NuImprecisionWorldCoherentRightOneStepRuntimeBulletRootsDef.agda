module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepRuntimeBulletRootsDef
  where

-- File Charter:
--   * Defines the two explicit target-leading one-step capabilities whose
--     source endpoints contain matched or source-only runtime bullets.
--   * Keeps the relation's allocation world, ambient prefix, current endpoint
--     typings, and complete lineage-carrying outcome visible.
--   * Omits a target-only runtime-bullet capability because its stored and
--     post-allocation type-imprecision indices are inconsistent.
--   * Contains no implementation, dispatcher, wrapper record, postulate,
--     hole, permissive option, or compatibility alias.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( StoreChange
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; ⇑ᵗᵐ
  ; _•
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


WorldCoherentRightOneStepMatchedRuntimeBulletᵀ : Set₁
WorldCoherentRightOneStepMatchedRuntimeBulletᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ N′ : Term} {A B : Ty}
    {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((⇑ᵗᵐ L) •) →
  RuntimeOK ((⇑ᵗᵐ L′) •) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ (⇑ᵗᵐ L) • ⊑ (⇑ᵗᵐ L′) •
      ⦂ A ⊑ B ∶ p →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ (⇑ᵗᵐ L) • ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ (⇑ᵗᵐ L′) • ⦂ B →
  (⇑ᵗᵐ L′) • —→[ χ ] N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (⇑ᵗᵐ L) •} {N′ = N′} {χ = χ} {ρ = ρ} p


WorldCoherentRightOneStepSourceRuntimeBulletᵀ : Set₁
WorldCoherentRightOneStepSourceRuntimeBulletᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L M′ N′ : Term} {A B : Ty}
    {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((⇑ᵗᵐ L) •) →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ (⇑ᵗᵐ L) • ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ (⇑ᵗᵐ L) • ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ B →
  M′ —→[ χ ] N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (⇑ᵗᵐ L) •} {N′ = N′} {χ = χ} {ρ = ρ} p
