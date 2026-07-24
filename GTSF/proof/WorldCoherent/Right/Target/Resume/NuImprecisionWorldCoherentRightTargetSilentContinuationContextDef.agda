module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSilentContinuationContextDef
  where

-- File Charter:
--   * Defines exact continuation after a source-silent right-value catch-up
--     has reached the initial endpoints of a second right-value catch-up.
--   * Exposes target-context action and right-only store-lineage witnesses
--     for both inputs and the composed result.
--   * Contains no implementation, new result carrier, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; Σ-syntax)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Types using (Ty; TyCtx)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix
  using (RightOnlyStoreImpPrefix)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( resultCtx
  ; resultStore
  ; resultSourceType
  ; resultTargetType
  ; sourceResult
  ; targetResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (lineageStore)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightTargetSilentContinuationContextᵀ : Set₁
WorldCoherentRightTargetSilentContinuationContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (first : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ} p) →
  let first-result =
        weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult first))
  in
  resultCtx first-result ≡
    applyRightImpCtxChanges (targetTailChanges first-result) Φ →
  RightOnlyStoreImpPrefix
    (lineageStore (worldRightCatchupStoreLineage first))
    (resultStore first-result) →
  (second : WorldCoherentRightValueCatchupIndexedResult
    {V = sourceResult first-result}
    {M′ = targetResult first-result}
    {ρ = resultStore first-result}
    (transportType first-result p)) →
  let second-result =
        weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult second))
  in
  resultCtx second-result ≡
    applyRightImpCtxChanges
      (targetTailChanges second-result)
      (resultCtx first-result) →
  RightOnlyStoreImpPrefix
    (lineageStore (worldRightCatchupStoreLineage second))
    (resultStore second-result) →
  Σ[ continued ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ} p ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult continued)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult continued))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage continued))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult continued))))
