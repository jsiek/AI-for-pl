module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetConversionFramesLemma
  where

-- File Charter:
--   * Exposes canonical exact target-conversion context frames for
--     target-oriented world-coherent one-step simulation.
--   * Keeps future dispatcher consumers independent of the implementation.
--   * Contains no wrapper relation, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetConversionFramesDef
  using (WorldCoherentRightOneStepTargetConversionFrames)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetConversionFramesProof
  using (world-coherent-right-one-step-target-conversion-frames-proofᵀ)


world-coherent-right-one-step-target-conversion-framesᵀ :
  WorldCoherentRightOneStepTargetConversionFrames
world-coherent-right-one-step-target-conversion-framesᵀ =
  world-coherent-right-one-step-target-conversion-frames-proofᵀ
