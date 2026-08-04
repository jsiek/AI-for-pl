module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  where

-- File Charter:
--   * Aggregates the direct paired reveal, conceal, widening, and quotient
--     value/value leaves for source function-cast beta.
--   * Retains exact quotient function-cast shapes, index composition, and
--     reduction-closed compatibility.
--   * Contains no implementation, relation view, postulate, hole, or
--     permissive option.

import Coercions as C
import CastImprecisionShape as CastShape
open import Data.List using ([])

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; Value; _·_; _⟨_⟩)
open import QuotientImprecisionCompatibility using
  (ReductionClosedQuotientWideningCompatible)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; TyCtx; _⇒_)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef
  using (WorldCoherentSourceOneStepOutcome)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedConcealValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedConcealValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedRevealValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedRevealValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ)


WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ : Set₁
WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d e f : C.Coercion}
    {D D′ A A′ B B′ : Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {s s′ : ImprecisionShape} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK ((L′ ⟨ e C.↦ f ⟩) · R′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺᵖ V ⊑ L′ ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ
    (c C.↦ d) (e C.↦ f)
    D D′ (A ⇒ B) (A′ ⇒ B′) →
  CastShape.widening CastShape.⊢ᶜ (c C.↦ d) ⦂ s →
  CastShape.widening CastShape.⊢ᶜ (e C.↦ f) ⦂ s′ →
  s ；⌊ pA ↦ pB ⌋≋ᵖ qD ； s′ →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ (c C.↦ d) (e C.↦ f)
    qD (pA ↦ pB) s s′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value W →
  Value L′ →
  Value R′ →
  WorldCoherentSourceOneStepOutcome
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = (L′ ⟨ e C.↦ f ⟩) · R′}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {χ = keep} {ρ = ρ} pB


record WorldCoherentSourceFunctionCastBetaPairedValues : Set₁ where
  field
    sourceFunctionCastBetaPairedRevealValuesCase :
      WorldCoherentSourceFunctionCastBetaPairedRevealValuesᵀ

    sourceFunctionCastBetaPairedConcealValuesCase :
      WorldCoherentSourceFunctionCastBetaPairedConcealValuesᵀ

    sourceFunctionCastBetaPairedWideningValuesCase :
      WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ

    sourceFunctionCastBetaPairedQuotientValuesCase :
      WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ

open WorldCoherentSourceFunctionCastBetaPairedValues public
