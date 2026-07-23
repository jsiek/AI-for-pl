module
  proof.NuImprecisionWorldCoherentSourceTargetKeepPrependDef
  where

-- File Charter:
--   * Defines prepending one target-only pure step to an exact source step.
--   * Leaves the completed source trace, final relation, and world unchanged.
--   * Contains no implementation, postulate, hole, or permissive option.

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceTargetKeepPrependᵀ : Set₁
WorldCoherentSourceTargetKeepPrependᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ N′ L : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} {χ} →
  M′ —→[ keep ] N′ →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = N′} {L = L}
    {A = A} {B = B} {χ = χ} {ρ = ρ} p →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = B} {χ = χ} {ρ = ρ} p
