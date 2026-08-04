module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextLemma
  where

-- File Charter:
--   * Exposes the canonical paired-lambda target-allocation context theorem.
--   * Assembles the canonical post-beta relation and complete source-bullet
--     right-allocation transport into the strict allocation proof.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, termination bypass, or broad DGG
--     import.

open import
  proof.Right.AllocationRuntime.NuImprecisionRightTargetAllocationSourceBulletTransportProof
  using (right-target-allocation-source-bullet-transport-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextProof
  using
  (world-coherent-right-target-widen-instantiation-paired-lambda-allocation-context-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextProof
  using
  (world-coherent-right-target-widen-instantiation-paired-lambda-post-beta-context-proofᵀ)


world-coherent-right-target-widen-instantiation-paired-lambda-allocation-contextᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextᵀ
world-coherent-right-target-widen-instantiation-paired-lambda-allocation-contextᵀ =
  world-coherent-right-target-widen-instantiation-paired-lambda-allocation-context-proofᵀ
    world-coherent-right-target-widen-instantiation-paired-lambda-post-beta-context-proofᵀ
    right-target-allocation-source-bullet-transport-proofᵀ
