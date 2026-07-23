module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependDef
  where

-- File Charter:
--   * Defines prepending one target-only pure step to a completed
--     world-coherent right-value catch-up.
--   * Reuses the existing catch-up result and keeps all final-world
--     invariants unchanged.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Types using (Ty; TyCtx)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightTargetKeepPrependᵀ : Set₁
WorldCoherentRightTargetKeepPrependᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ N′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  M′ —→[ keep ] N′ →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = N′} {ρ = ρ} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ} p
