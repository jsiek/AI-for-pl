module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepPrimitiveFramesLemma
  where

-- File Charter:
--   * Exposes the canonical target-oriented world-coherent primitive frames.
--   * Keeps future dispatcher consumers independent of the implementation
--     module.
--   * Contains no wrapper relation, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepPrimitiveFramesDef
  using (WorldCoherentRightOneStepPrimitiveFrames)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepPrimitiveFramesProof
  using (world-coherent-right-one-step-primitive-frames-proofᵀ)


world-coherent-right-one-step-primitive-framesᵀ :
  WorldCoherentRightOneStepPrimitiveFrames
world-coherent-right-one-step-primitive-framesᵀ =
  world-coherent-right-one-step-primitive-frames-proofᵀ
