module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaRootContextLemma
  where

-- File Charter:
--   * Exposes the canonical contextual paired-lambda target-instantiation
--     root theorem.
--   * Assembles the canonical target-allocation context and target-`keep`
--     prepend capabilities into the strict higher-order root proof.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, termination bypass, or broad DGG
--     import.

open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependContextLemma
  using (world-coherent-right-target-keep-prepend-contextᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaAllocationContextLemma
  using
  (world-coherent-right-target-widen-instantiation-paired-lambda-allocation-contextᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaRootContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaRootContextProof
  using
  (world-coherent-right-target-widen-instantiation-paired-lambda-root-context-proofᵀ)


world-coherent-right-target-widen-instantiation-paired-lambda-root-contextᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedLambdaRootContextᵀ
world-coherent-right-target-widen-instantiation-paired-lambda-root-contextᵀ =
  world-coherent-right-target-widen-instantiation-paired-lambda-root-context-proofᵀ
    world-coherent-right-target-widen-instantiation-paired-lambda-allocation-contextᵀ
    world-coherent-right-target-keep-prepend-contextᵀ
