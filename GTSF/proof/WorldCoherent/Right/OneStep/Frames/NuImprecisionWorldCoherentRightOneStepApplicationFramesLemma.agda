module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepApplicationFramesLemma
  where

-- File Charter:
--   * Exposes the canonical target-oriented world-coherent application frames.
--   * Keeps future dispatcher consumers independent of the implementation
--     module.
--   * Contains no wrapper relation, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepApplicationFramesDef
  using (WorldCoherentRightOneStepApplicationFrames)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepApplicationFramesProof
  using (world-coherent-right-one-step-application-frames-proofᵀ)


world-coherent-right-one-step-application-framesᵀ :
  WorldCoherentRightOneStepApplicationFrames
world-coherent-right-one-step-application-framesᵀ =
  world-coherent-right-one-step-application-frames-proofᵀ
