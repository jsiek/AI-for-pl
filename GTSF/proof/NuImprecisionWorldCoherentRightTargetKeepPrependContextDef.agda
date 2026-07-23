module
  proof.NuImprecisionWorldCoherentRightTargetKeepPrependContextDef
  where

-- File Charter:
--   * Defines context-preserving prepending of one target-only pure step to
--     a completed right-value catch-up.
--   * Exposes the target-change context action inline and reuses the existing
--     complete catch-up carrier.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; Σ-syntax)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.NuImprecisionSimulationResultDef using
  (resultCtx; resultStore; targetTailChanges; weakIndexedResult)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (lineageStore)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightTargetKeepPrependContextᵀ : Set₁
WorldCoherentRightTargetKeepPrependContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ N′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  M′ —→[ keep ] N′ →
  (caught : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = N′} {ρ = ρ} p) →
  resultCtx
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult caught)))
    ≡
  applyRightImpCtxChanges
    (targetTailChanges
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult caught))))
    Φ →
  RightOnlyStoreImpPrefix
    (lineageStore
      (worldRightCatchupStoreLineage caught))
    (resultStore
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult caught)))) →
  Σ[ prepended ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ} p ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult prepended)))
      ≡
    applyRightImpCtxChanges
      (targetTailChanges
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult prepended))))
      Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore
        (worldRightCatchupStoreLineage prepended))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult prepended))))
