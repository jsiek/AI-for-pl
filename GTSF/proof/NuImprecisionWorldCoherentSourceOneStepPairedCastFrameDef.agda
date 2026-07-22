module
  proof.NuImprecisionWorldCoherentSourceOneStepPairedCastFrameDef
  where

-- File Charter:
--   * Defines paired source/target cast framing for one completed source step.
--   * Consumes and returns the existing complete continuing result directly.
--   * Contains no outcome wrapper, implementation, recursion, postulate,
--     hole, permissive option, or compatibility alias.

open import Coercions using (Coercion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (StoreChange; applyCoercion)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  (PairedCast; StoreImpPrefix)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceOneStepPairedCastFrameᵀ : Set₁
WorldCoherentSourceOneStepPairedCastFrameᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ L : Term} {A A′ B B′ : Ty}
    {c c′ : Coercion} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  PairedCast Φ Δᴸ Δᴿ ρ₀ c c′ p q →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M ⟨ c ⟩} {M′ = M′ ⟨ c′ ⟩}
    {L = L ⟨ applyCoercion χ c ⟩}
    {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q
