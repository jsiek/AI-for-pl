module
  proof.NuImprecisionWorldCoherentRightTargetKeepPrependProof
  where

-- File Charter:
--   * Proves target-only pure-step prepending for world-coherent right-value
--     catch-up by extending only the target trace.
--   * Preserves the indexed relation, transport, type coherence, lineage,
--     source-bullet transport, and final-world invariants definitionally.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad simulation import.

open import Data.List using (_∷_)
open import NuReduction using (keep; ↠-step; _—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Types using (Ty)
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( right-value-indexed-catchup
  ; RightValueCatchupIndexedResult
  )
open import
  proof.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import proof.NuImprecisionSimulationResultDef
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef
open import
  proof.NuImprecisionWorldCoherentRightTargetKeepPrependDef
  using (WorldCoherentRightTargetKeepPrependᵀ)


private
  prepend-target-keep-result :
    ∀ {Φ Δᴸ Δᴿ V M′ N′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ} →
    M′ —→[ keep ] N′ →
    WeakOneStepResult ρ V N′ A B keep →
    WeakOneStepResult ρ V M′ A B keep
  prepend-target-keep-result target→ result =
    record
      { sourceChanges = sourceChanges result
      ; targetTailChanges = keep ∷ targetTailChanges result
      ; sourceResult = sourceResult result
      ; targetResult = targetResult result
      ; resultCtx = resultCtx result
      ; resultLeftCtx = resultLeftCtx result
      ; resultRightCtx = resultRightCtx result
      ; sourceCtxResult = sourceCtxResult result
      ; targetCtxResult = targetCtxResult result
      ; resultStore = resultStore result
      ; resultSourceType = resultSourceType result
      ; resultTargetType = resultTargetType result
      ; sourceTypeResult = sourceTypeResult result
      ; targetTypeResult = targetTypeResult result
      ; transportType = transportType result
      ; transportAllBody = transportAllBody result
      ; transportRightBody = transportRightBody result
      ; resultType = resultType result
      ; sourceCatchup = sourceCatchup result
      ; targetTail = ↠-step target→ (targetTail result)
      ; sourceStoreResult = sourceStoreResult result
      ; targetStoreResult = targetStoreResult result
      ; relatedResults = relatedResults result
      }


world-coherent-right-target-keep-prepend-proofᵀ :
  WorldCoherentRightTargetKeepPrependᵀ
world-coherent-right-target-keep-prepend-proofᵀ
    target→
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result result canonical)
        source-empty source-unchanged vV noV vV′ noV′
        transport coherence)
      lineage bullet coherent exclusive unique wfR) =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup
      (weak-indexed-result prepended canonical)
      source-empty source-unchanged vV noV vV′ noV′
      prepended-transport prepended-coherence)
    prepended-lineage prepended-bullet
    coherent exclusive unique wfR
  where
  prepended = prepend-target-keep-result target→ result

  prepended-transport =
    weak-step-transport (transportNo•Terms transport)

  prepended-coherence =
    weak-step-type-coherence
      (transportArrowCoherent coherence)
      (transportAllCoherent coherence)

  prepended-lineage : WeakOneStepStoreLineage prepended
  prepended-lineage =
    weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage)

  prepended-bullet :
    RightValueCatchupSourceBulletTransportᵀ prepended
  prepended-bullet =
    λ prefix okL noM′ L⊢ L⊑M′ →
      bullet prefix okL noM′ L⊢ L⊑M′
