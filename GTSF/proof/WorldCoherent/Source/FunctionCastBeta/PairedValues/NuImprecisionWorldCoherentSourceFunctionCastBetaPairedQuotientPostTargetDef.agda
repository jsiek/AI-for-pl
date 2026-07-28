module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedQuotientPostTargetDef
  where

-- File Charter:
--   * Defines the shared operational paired-quotient function-beta boundary
--     after the target function-cast beta step has already occurred.
--   * Retains the outer quotient compatibility needed to eliminate one
--     paired quotient function layer through bilateral reduction.
--   * Returns the ordinary source-step outcome; no quotient catch-up result
--     escapes this boundary.
--   * Contains no implementation, helper carrier, postulate, hole, or
--     permissive option.

import CastImprecisionShape as CastShape
import Coercions as C
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
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef
  using (WorldCoherentSourceOneStepOutcome)


WorldCoherentSourceFunctionCastBetaPairedQuotientPostTargetᵀ : Set₁
WorldCoherentSourceFunctionCastBetaPairedQuotientPostTargetᵀ =
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
  RuntimeOK ((L′ · (R′ ⟨ e ⟩)) ⟨ f ⟩) →
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
    {M′ = (L′ · (R′ ⟨ e ⟩)) ⟨ f ⟩}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {χ = keep} {ρ = ρ} pB
