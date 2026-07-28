module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientFrameRecursionDef
  where

-- File Charter:
--   * Defines the prefix-aware recursive boundary for a target step beneath
--     an `up⊑upᵀ` quotient-widening pair.
--   * Keeps QTIP and widening evidence at the base relational store while
--     the current world, runtime facts, and outcome live at its extension.
--   * Contains no implementation, active-value synchronization, dispatcher,
--     postulate, hole, permissive option, or theorem-fragment alias.

open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion)
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (StoreChange; applyCoercion; _—→[_]_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx)
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


WorldCoherentRightOneStepQuotientFrameRecursionᵀ : Set₁
WorldCoherentRightOneStepQuotientFrameRecursionᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {N N′ L′ : Term} {D D′ A A′ : Ty}
    {u u′ : Coercion} {s s′}
    {χ : StoreChange}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreImpPrefix ρᵇ ρ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (N ⟨ u ⟩) →
  RuntimeOK (N′ ⟨ u′ ⟩) →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ N ⟨ u ⟩ ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ N′ ⟨ u′ ⟩ ⦂ A′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺᵖ N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
  widening ⊢ᶜ u ⦂ s →
  widening ⊢ᶜ u′ ⦂ s′ →
  s ；⌊ pA ⌋≋ᵖ qD ； s′ →
  N′ —→[ χ ] L′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = N ⟨ u ⟩}
    {N′ = L′ ⟨ applyCoercion χ u′ ⟩}
    {χ = χ} {ρ = ρ} pA
