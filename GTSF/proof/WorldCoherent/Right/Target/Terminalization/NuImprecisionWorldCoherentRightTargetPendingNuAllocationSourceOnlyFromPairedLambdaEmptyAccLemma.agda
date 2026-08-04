module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedLambdaEmptyAccLemma
  where

-- File Charter:
--   * Exposes the canonical ranked direct paired-lambda inert empty-tail
--     target-`ν` allocation cell.
--   * Supplies the completed contextual paired-lambda allocation theorem to
--     the strict higher-order cell proof.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, termination bypass, or broad DGG
--     import.

open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationAccCellsDef
  using
  (WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedLambdaEmptyAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedLambdaEmptyAccProof
  using
  (world-coherent-right-target-pending-nu-allocation-source-only-from-paired-lambda-empty-acc-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextLemma
  using
  (world-coherent-right-target-widen-instantiation-paired-lambda-allocation-contextᵀ)


world-coherent-right-target-pending-nu-allocation-source-only-from-paired-lambda-empty-accᵀ :
  WorldCoherentRightTargetPendingNuAllocationSourceOnlyFromPairedLambdaEmptyAccᵀ
world-coherent-right-target-pending-nu-allocation-source-only-from-paired-lambda-empty-accᵀ =
  world-coherent-right-target-pending-nu-allocation-source-only-from-paired-lambda-empty-acc-proofᵀ
    world-coherent-right-target-widen-instantiation-paired-lambda-allocation-contextᵀ
