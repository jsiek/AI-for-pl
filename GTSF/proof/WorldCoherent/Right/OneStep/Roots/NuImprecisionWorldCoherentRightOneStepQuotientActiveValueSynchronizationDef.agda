module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueSynchronizationDef
  where

-- File Charter:
--   * Defines the prefix-aware active-value synchronization boundary for an
--     `up⊑upᵀ` quotient-widening pair.
--   * Keeps QTIP and widening evidence at the base relational store while
--     the current world, runtime facts, and outcome live at its extension.
--   * Contains no frame recursion, implementation, dispatcher, postulate,
--     hole, permissive option, or theorem-fragment alias.

open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion)
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
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


WorldCoherentRightOneStepQuotientActiveValueSynchronizationᵀ : Set₁
WorldCoherentRightOneStepQuotientActiveValueSynchronizationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ L′ : Term} {D D′ A A′ : Ty}
    {u u′ : Coercion} {s s′}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreImpPrefix ρᵇ ρ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (N ⟨ u ⟩) →
  RuntimeOK (V′ ⟨ u′ ⟩) →
  Value V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺᵖ N ⊑ V′ ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
  widening ⊢ᶜ u ⦂ s →
  widening ⊢ᶜ u′ ⦂ s′ →
  s ；⌊ pA ⌋≋ᵖ qD ； s′ →
  V′ ⟨ u′ ⟩ —→ L′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = N ⟨ u ⟩} {N′ = L′}
    {χ = keep} {ρ = ρ} pA
