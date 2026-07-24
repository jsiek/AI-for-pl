module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingAllocationContinuationContextDef
  where

-- File Charter:
--   * States exact source-silent continuation from a raw paired-lambda
--     pending-allocation prefix into a recursive world-coherent right-value
--     catch-up at the prefix's result store, terms, types, and index.
--   * Keeps the raw prefix distinct from a right-value catch-up because its
--     pending target result need not yet be a value.
--   * Returns the contextual catch-up, target-context action, and right-only
--     lineage prefix for the original pending allocation.
--   * Contains no implementation, result/view/outcome type, named conclusion
--     alias, postulate, hole, permissive option, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; ⇑ᶜ)
open import Data.List using (List; []; map)
open import Data.Product using (_×_; Σ-syntax)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; Λ_; _⟨_⟩)
open import Types using (Ty; TyCtx; ★)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; resultCtx
  ; resultStore
  ; resultType
  ; sourceChanges
  ; sourceResult
  ; targetResult
  ; targetTailChanges
  ; weakIndexedResult
  )
open import
  proof.Right.Core.NuImprecisionRightContextAction
  using (applyRightImpCtxChanges)
open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix
  using (RightOnlyStoreImpPrefix)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (WeakOneStepStoreLineage; lineageStore)
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


WorldCoherentRightTargetPendingAllocationContinuationContextᵀ : Set₁
WorldCoherentRightTargetPendingAllocationContinuationContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {D F : Ty}
    {s : Coercion} {cs : List Coercion}
    {t : Φ ∣ Δᴸ ⊢ D ⊑ F ⊣ Δᴿ} →
  (first-indexed :
    WeakOneStepIndexedResult
      {M = Λ W}
      {N′ =
        applyTargetPendingCasts
          (NuTerms.ν ★ (Λ W′) s) cs}
      {χ = keep}
      {ρ = ρ}
      t) →
  let first = weakIndexedResult first-indexed
  in
  sourceChanges first ≡ [] →
  sourceResult first ≡ Λ W →
  targetResult first ≡
    applyTargetPendingCasts
      (W′ ⟨ s ⟩) (map ⇑ᶜ cs) →
  (first-lineage : WeakOneStepStoreLineage first) →
  RightValueCatchupSourceBulletTransportᵀ first →
  resultCtx first ≡
    applyRightImpCtxChanges
      (targetTailChanges first) Φ →
  RightOnlyStoreImpPrefix
    (lineageStore first-lineage) (resultStore first) →
  (continued :
    WorldCoherentRightValueCatchupIndexedResult
      {V = sourceResult first}
      {M′ = targetResult first}
      {ρ = resultStore first}
      (resultType first)) →
  let second =
        weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult continued))
  in
  resultCtx second ≡
    applyRightImpCtxChanges
      (targetTailChanges second)
      (resultCtx first) →
  RightOnlyStoreImpPrefix
    (lineageStore
      (worldRightCatchupStoreLineage continued))
    (resultStore second) →
  Σ[ resumed ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = Λ W}
      {M′ =
        applyTargetPendingCasts
          (NuTerms.ν ★ (Λ W′) s) cs}
      {ρ = ρ}
      t ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult resumed)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult resumed))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore
        (worldRightCatchupStoreLineage resumed))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult resumed))))
