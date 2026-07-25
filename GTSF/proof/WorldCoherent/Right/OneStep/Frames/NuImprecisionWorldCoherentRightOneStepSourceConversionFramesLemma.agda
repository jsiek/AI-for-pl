module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesLemma
  where

-- File Charter:
--   * Exposes the canonical exact source-conversion frame capability.
--   * Contains no implementation, recursion, postulate, hole, or permissive
--     option.

open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesDef
  using (WorldCoherentRightOneStepSourceConversionFrames)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesProof
  using (world-coherent-right-one-step-source-conversion-frames-proofᵀ)


world-coherent-right-one-step-source-conversion-framesᵀ :
  WorldCoherentRightOneStepSourceConversionFrames
world-coherent-right-one-step-source-conversion-framesᵀ =
  world-coherent-right-one-step-source-conversion-frames-proofᵀ
