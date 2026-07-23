module
  proof.NuImprecisionWorldCoherentSourceTargetKeepPrependProof
  where

-- File Charter:
--   * Implements target-only pure-step prepending by extending targetTail.
--   * Reuses every completed source and final-world witness definitionally.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import Data.List using (_∷_)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (StoreChange; keep; ↠-step; _—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; canonicalIndexedResults
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; sourceTypeResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; targetTypeResult
  ; transportAllBody
  ; transportRightBody
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weak-step-transport
  ; weak-step-type-coherence
  ; transportNo•Terms
  ; transportAllCoherent
  ; transportArrowCoherent
  )
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( sourceStepAssumptionMembershipUnique
  ; sourceStepChangesExact
  ; sourceStepIndexedResult
  ; sourceStepResultExact
  ; sourceStepSourceNameExclusive
  ; sourceStepStoreLineage
  ; sourceStepTransport
  ; sourceStepTypeCoherence
  ; sourceStepWorldCoherent
  ; world-coherent-source-one-step-indexed
  )
open import
  proof.NuImprecisionWorldCoherentSourceTargetKeepPrependDef
  using (WorldCoherentSourceTargetKeepPrependᵀ)


prepend-target-keep-result :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ N′ : Term} {A B : Ty} {χ : StoreChange}
    (result : WeakOneStepResult ρ M N′ A B χ) →
  M′ —→[ keep ] N′ →
  WeakOneStepResult ρ M M′ A B χ
prepend-target-keep-result result target→ = record
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


world-coherent-source-target-keep-prepend-proofᵀ :
  WorldCoherentSourceTargetKeepPrependᵀ
world-coherent-source-target-keep-prepend-proofᵀ
    {p = p} target→ complete =
  world-coherent-source-one-step-indexed
    indexed transport coherence lineage
    (sourceStepChangesExact complete)
    (sourceStepResultExact complete)
    (sourceStepWorldCoherent complete)
    (sourceStepSourceNameExclusive complete)
    (sourceStepAssumptionMembershipUnique complete)
  where
  old-indexed = sourceStepIndexedResult complete
  old-result = weakIndexedResult old-indexed
  new-result = prepend-target-keep-result old-result target→

  indexed : WeakOneStepIndexedResult p
  indexed =
    weak-indexed-result new-result
      (canonicalIndexedResults old-indexed)

  transport : WeakOneStepTransport new-result
  transport =
    weak-step-transport
      (transportNo•Terms (sourceStepTransport complete))

  coherence : WeakOneStepTypeCoherence new-result
  coherence =
    weak-step-type-coherence
      (transportArrowCoherent (sourceStepTypeCoherence complete))
      (transportAllCoherent (sourceStepTypeCoherence complete))

  lineage : WeakOneStepStoreLineage new-result
  lineage =
    weak-step-store-lineage
      (lineageStore (sourceStepStoreLineage complete))
      (lineageEmbedding (sourceStepStoreLineage complete))
      (lineagePrefix (sourceStepStoreLineage complete))
