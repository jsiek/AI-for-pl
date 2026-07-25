module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualProof
  where

-- File Charter:
--   * Consumes one observed indexed target step from a completed
--     world-coherent right-value catch-up by reduction determinism.
--   * Removes the matching target-trace head while retaining source-bullet
--     transport, relational-store lineage, and all final-world invariants.
--   * Contains no dispatcher, recursion, postulate, hole, permissive option,
--     compatibility alias, or termination bypass.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import ImprecisionComposition using (⌊_⌋)
open import NuReduction using (↠-refl; ↠-step)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import proof.DGG.Core.NuReductionDeterminism using
  (step-deterministic; value-irreducible)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-target
  )
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (right-value-indexed-catchup)
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
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualDef
  using
  ( WorldCoherentRightTargetIndexedStepResidualᵀ
  ; world-coherent-right-target-indexed-step-residual
  )
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  (world-coherent-right-value-indexed-catchup)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)


world-coherent-right-target-indexed-step-residual-proofᵀ :
  WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ →
  WorldCoherentRightTargetIndexedStepResidualᵀ
world-coherent-right-target-indexed-step-residual-proofᵀ
    runtime-transport root
    caught@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result result canonical transport coherence)
        source-empty source-unchanged source-value source-no
        target-value target-no)
      lineage bullet final-coherent final-exclusive final-unique final-wfR)
    with targetTail result
world-coherent-right-target-indexed-step-residual-proofᵀ
    runtime-transport root
    caught@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result result canonical transport coherence)
        source-empty source-unchanged source-value source-no
        target-value target-no)
      lineage bullet final-coherent final-exclusive final-unique final-wfR)
    | ↠-refl =
  ⊥-elim (value-irreducible target-value root)
world-coherent-right-target-indexed-step-residual-proofᵀ
    runtime-transport root
    caught@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result result canonical transport coherence)
        source-empty source-unchanged source-value source-no
        target-value target-no)
      lineage bullet final-coherent final-exclusive final-unique final-wfR)
    | ↠-step target-step residual
    with step-deterministic root target-step
world-coherent-right-target-indexed-step-residual-proofᵀ
    runtime-transport root
    caught@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        (weak-indexed-result result canonical transport coherence)
        source-empty source-unchanged source-value source-no
        target-value target-no)
      lineage bullet final-coherent final-exclusive final-unique final-wfR)
    | ↠-step target-step residual
    | refl , refl =
  world-coherent-right-target-indexed-step-residual
    (weak-indexed-result residual-result canonical
      residual-transport residual-coherence)
    source-empty source-unchanged source-value source-no
    target-value target-no
    residual-lineage bullet
    (λ prefix okM noM′ M⊢ M⊑M′ →
      runtime-transport prefix okM noM′ M⊢ M⊑M′ caught)
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

  outer-unique =
    assumption-membership-unique→precision-index-unique final-unique

  target-unique =
    assumption-membership-unique→precision-index-unique
      (assumption-membership-unique-target final-unique)

  residual-coherence =
    weak-step-type-coherence
      (λ pC pD → outer-unique _ _)
      (λ q → outer-unique _ _)
      (λ p →
        trans (cong (λ q → ⌊ q ⌋) (outer-unique _ _))
          (transportShapeCoherent coherence p))
      (λ p →
        trans (cong (λ q → ⌊ q ⌋) (target-unique _ _))
          (transportRightBodyShapeCoherent coherence p))
      (transportLeftReplacementCoherent coherence)
      (transportRightReplacementCoherent coherence)
      (transportPairedReplacementCoherent coherence)
      (transportAllBodyPairedReplacementCoherent coherence)
      (transportSourceNuBodyLeftReplacementCoherent coherence)
      (transportRightBodyRightReplacementCoherent coherence)

  residual-lineage : WeakOneStepStoreLineage residual-result
  residual-lineage =
    weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage)
