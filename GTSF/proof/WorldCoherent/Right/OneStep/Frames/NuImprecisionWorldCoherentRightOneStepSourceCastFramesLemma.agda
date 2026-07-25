module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesLemma
  where

-- File Charter:
--   * Exposes canonical exact source cast frames for target-oriented
--     world-coherent one-step simulation.
--   * Keeps future dispatcher consumers independent of the implementation.
--   * Contains no wrapper relation, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesDef
  using (WorldCoherentRightOneStepSourceCastFrames)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesProof
  using (world-coherent-right-one-step-source-cast-frames-proofᵀ)


world-coherent-right-one-step-source-cast-framesᵀ :
  WorldCoherentRightOneStepSourceCastFrames
world-coherent-right-one-step-source-cast-framesᵀ =
  world-coherent-right-one-step-source-cast-frames-proofᵀ
