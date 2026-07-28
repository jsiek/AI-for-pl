module
  proof.WorldCoherent.Source.FunctionCastBeta.Direct.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectDef
  where

-- File Charter:
--   * Defines source function-cast beta scheduling when QTI inversion exposes
--     a target application directly.
--   * Permits the target trace required by paired function casts; it does not
--     require the target redex to remain unchanged.
--   * Propagates source blame reached while terminalizing exposed domain
--     casts after function catch-up.
--   * Contains no implementation, postulate, hole, or
--     permissive option.

import Coercions as C
open import Data.List using ([])

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
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (_∣_∣_⊢_⦂_)
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


WorldCoherentSourceFunctionCastBetaDirectᵀ : Set₁
WorldCoherentSourceFunctionCastBetaDirectᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK (L′ · R′) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ []
    ⊢ (V ⟨ c C.↦ d ⟩) · W ⦂ B →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ L′ · R′ ⦂ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⟨ c C.↦ d ⟩ ⊑ L′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value W →
  WorldCoherentSourceOneStepOutcome
    {M = (V ⟨ c C.↦ d ⟩) · W}
    {M′ = L′ · R′}
    {L = (V · (W ⟨ c ⟩)) ⟨ d ⟩}
    {χ = keep} {ρ = ρ⁺} pB
