module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetPureStepResidualProof
  where

-- File Charter:
--   * Proves pure target-step residualization by reduction determinism.
--   * Removes the matching head from the target trace and preserves its
--     indexed relation, lineage, source-bullet transport, and final world.
--   * Contains no dispatcher, postulate, hole, permissive option, or
--     termination bypass.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import NuReduction using (keep; pure-step; ↠-refl; ↠-step)
open import proof.DGG.Core.NuReductionDeterminism using
  (pure-value-irreducible; step-deterministic)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (right-value-indexed-catchup)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetPureStepResidualDef
  using (WorldCoherentRightTargetPureStepResidualᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( world-coherent-right-value-indexed-catchup
  )


world-coherent-right-target-pure-step-residual-proofᵀ :
  WorldCoherentRightTargetPureStepResidualᵀ
world-coherent-right-target-pure-step-residual-proofᵀ
    root
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result result canonical transport coherence)
        source-empty source-unchanged source-value source-no
        target-value target-no)
      lineage bullet final-coherent final-exclusive final-unique final-wfR)
    with targetTail result
world-coherent-right-target-pure-step-residual-proofᵀ
    root
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result result canonical transport coherence)
        source-empty source-unchanged source-value source-no
        target-value target-no)
      lineage bullet final-coherent final-exclusive final-unique final-wfR)
    | ↠-refl =
  ⊥-elim (pure-value-irreducible target-value root)
world-coherent-right-target-pure-step-residual-proofᵀ
    root
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result result canonical transport coherence)
        source-empty source-unchanged source-value source-no
        target-value target-no)
      lineage bullet final-coherent final-exclusive final-unique final-wfR)
    | ↠-step target-step residual
    with step-deterministic (pure-step root) target-step
world-coherent-right-target-pure-step-residual-proofᵀ
    root
    (world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result result canonical transport coherence)
        source-empty source-unchanged source-value source-no
        target-value target-no)
      lineage bullet final-coherent final-exclusive final-unique final-wfR)
    | ↠-step target-step residual
    | refl , refl =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup
      (weak-indexed-result residual-indexed canonical
        residual-transport residual-coherence)
      source-empty source-unchanged source-value source-no
      target-value target-no)
    residual-lineage residual-bullet
    final-coherent final-exclusive final-unique final-wfR
  where
  residual-result =
    weak-step-result
      (sourceChanges result)
      _
      (sourceResult result)
      (targetResult result)
      (resultCtx result)
      (resultLeftCtx result)
      (resultRightCtx result)
      (sourceCtxResult result)
      (targetCtxResult result)
      (resultStore result)
      (resultSourceType result)
      (resultTargetType result)
      (sourceTypeResult result)
      (targetTypeResult result)
      (transportType result)
      (transportAllBody result)
      (transportRightBody result)
      (transportSourceNu result)
      (resultType result)
      (sourceCatchup result)
      residual
      (sourceStoreResult result)
      (targetStoreResult result)
      (relatedResults result)

  residual-transport =
    weak-step-transport (transportNo•Terms transport)

  residual-coherence =
    weak-step-type-coherence
      (transportArrowCoherent coherence)
      (transportAllCoherent coherence)
      (transportShapeCoherent coherence)
      (transportRightBodyShapeCoherent coherence)
      (transportLeftReplacementCoherent coherence)
      (transportRightReplacementCoherent coherence)
      (transportPairedReplacementCoherent coherence)
      (transportAllBodyPairedReplacementCoherent coherence)
      (transportSourceNuBodyLeftReplacementCoherent coherence)
      (transportRightBodyRightReplacementCoherent coherence)

  residual-indexed = residual-result

  residual-lineage : WeakOneStepStoreLineage residual-result
  residual-lineage =
    weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage)

  residual-bullet :
    RightValueCatchupSourceBulletTransportᵀ residual-result
  residual-bullet prefix okL noM′ L⊢ L⊑M′ =
    bullet prefix okL noM′ L⊢ L⊑M′
