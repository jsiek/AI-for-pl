module
  proof.NuImprecisionWorldCoherentSourceOneStepQuotientDownUpStepDef
  where

-- File Charter:
--   * Defines the fused quotient down/up source-step boundary.
--   * Returns the existing ordinary source-step outcome after eliminating the
--     quotient subjudgment internally; no quotient result carrier escapes.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility alias.

open import Coercions using (Coercion)
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (StoreChange; applyCoercion; _—→[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (RuntimeOK; Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepOutcomeDef using
  (WorldCoherentSourceOneStepOutcome)
open import proof.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)


WorldCoherentSourceOneStepQuotientDownUpStepᵀ : Set₁
WorldCoherentSourceOneStepQuotientDownUpStepᵀ =
  WorldCoherentSourceOneStepPrefixᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {D D′ A A′ : Ty}
    {u u′ : Coercion} {χ : StoreChange}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M ⟨ u ⟩) →
  RuntimeOK (M′ ⟨ u′ ⟩) →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ M ⟨ u ⟩ ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⟨ u′ ⟩ ⦂ A′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  M —→[ χ ] L →
  WorldCoherentSourceOneStepOutcome
    {M = M ⟨ u ⟩} {M′ = M′ ⟨ u′ ⟩}
    {L = L ⟨ applyCoercion χ u ⟩}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} pA
