module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetPureStepResidualDef
  where

-- File Charter:
--   * Defines removal of one observed pure target step from a completed
--     world-coherent right-value catch-up.
--   * Keeps the completed target value and all final-world invariants.
--   * Contains no implementation, result wrapper, postulate, hole,
--     permissive option, or broad simulation import.

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (_—→_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using (Term)
open import Types using (Ty; TyCtx)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightTargetPureStepResidualᵀ : Set₁
WorldCoherentRightTargetPureStepResidualᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ N′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  M′ —→ N′ →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = N′} {ρ = ρ} p
