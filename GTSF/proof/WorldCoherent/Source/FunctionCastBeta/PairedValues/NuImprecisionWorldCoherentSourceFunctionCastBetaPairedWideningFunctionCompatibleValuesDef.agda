module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesDef
  where

-- File Charter:
--   * Defines paired-widening value beta when the hereditary function
--     compatibility constructor exposes codomain compatibility.
--   * Contains no implementation, result/view carrier, postulate, hole, or
--     permissive option.

import Coercions as C
import CastImprecisionShape as CastShape
open import Data.List using ([])

open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _↦ˢ_; _；_≋_)
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; Term; Value; _·_; _⟨_⟩)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; _⇒_)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesᵀ :
  Set₁
WorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d e f : C.Coercion}
    {A₀ A₀′ A A′ B₀ B₀′ B B′ : Ty}
    {pA₀ : Φ ∣ Δᴸ ⊢ A₀ ⊑ A₀′ ⊣ Δᴿ}
    {pB₀ : Φ ∣ Δᴸ ⊢ B₀ ⊑ B₀′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {c-shape d-shape e-shape f-shape r : ImprecisionShape} {μ μ′} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK ((L′ ⟨ e C.↦ f ⟩) · R′) →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρᵇ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ
    ⊢ c C.↦ d ∶ A₀ ⇒ B₀ ⊑ A ⇒ B →
  CastShape.widening CastShape.⊢ᶜ
    c C.↦ d ⦂ c-shape ↦ˢ d-shape →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ
    ⊢ e C.↦ f ∶ A₀′ ⇒ B₀′ ⊑ A′ ⇒ B′ →
  CastShape.widening CastShape.⊢ᶜ
    e C.↦ f ⦂ e-shape ↦ˢ f-shape →
  (c-shape ↦ˢ d-shape) ； ⌊ pA ↦ pB ⌋ ≋ r →
  ⌊ pA₀ ↦ pB₀ ⌋ ； (e-shape ↦ˢ f-shape) ≋ r →
  PairedWideningCompatible
    Φ Δᴸ Δᴿ d f pB₀ pB d-shape f-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ V ⊑ L′
      ⦂ A₀ ⇒ B₀ ⊑ A₀′ ⇒ B₀′ ∶ pA₀ ↦ pB₀ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value W →
  Value L′ →
  Value R′ →
  WorldCoherentSourceOneStepIndexedResult
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = (L′ ⟨ e C.↦ f ⟩) · R′}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {χ = keep} {ρ = ρ} pB
