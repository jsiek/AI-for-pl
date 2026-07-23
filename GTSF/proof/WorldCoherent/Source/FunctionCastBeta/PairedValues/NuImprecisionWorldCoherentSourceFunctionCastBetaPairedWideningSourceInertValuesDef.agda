module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesDef
  where

-- File Charter:
--   * Defines the source-inert half of paired-widening value beta.
--   * Isolates the only paired-widening compatibility alternative that does
--     not expose the componentwise source-output/target-input bridge.
--   * Contains no implementation, result/view carrier, postulate, hole, or
--     permissive option.

import Coercions as C
open import Coercions using (Inert)
open import Data.List using ([])

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


WorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesᵀ :
  Set₁
WorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d e f : C.Coercion}
    {A₀ A₀′ A A′ B₀ B₀′ B B′ : Ty}
    {pA₀ : Φ ∣ Δᴸ ⊢ A₀ ⊑ A₀′ ⊣ Δᴿ}
    {pB₀ : Φ ∣ Δᴸ ⊢ B₀ ⊑ B₀′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {μ μ′} →
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
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ
    ⊢ e C.↦ f ∶ A₀′ ⇒ B₀′ ⊑ A′ ⇒ B′ →
  Inert (c C.↦ d) →
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
