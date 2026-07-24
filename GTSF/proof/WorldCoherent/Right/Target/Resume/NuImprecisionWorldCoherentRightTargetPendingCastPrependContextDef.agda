module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextDef
  where

-- File Charter:
--   * Defines contextual prepending of one target `keep` step beneath an
--     arbitrary pending target-cast list.
--   * Reuses the existing complete catch-up carrier and exposes the target
--     context action and right-only lineage witnesses.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion)
open import Data.List using (List)
open import Data.Product using (_×_; Σ-syntax)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Types using (Ty; TyCtx)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  (resultCtx; resultStore; targetTailChanges; weakIndexedResult)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (lineageStore)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (applyTargetPendingCasts)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightTargetPendingCastPrependContextᵀ : Set₁
WorldCoherentRightTargetPendingCastPrependContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ N′ : Term} {A B : Ty} {cs : List Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  M′ —→[ keep ] N′ →
  (caught : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = applyTargetPendingCasts N′ cs} {ρ = ρ} p) →
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
    (lineageStore (worldRightCatchupStoreLineage caught))
    (resultStore
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult caught)))) →
  Σ[ prepended ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = applyTargetPendingCasts M′ cs} {ρ = ρ} p ]
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
      (lineageStore (worldRightCatchupStoreLineage prepended))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult prepended))))
