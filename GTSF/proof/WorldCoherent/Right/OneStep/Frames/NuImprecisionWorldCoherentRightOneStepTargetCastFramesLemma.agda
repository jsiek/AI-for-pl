module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetCastFramesLemma
  where

-- File Charter:
--   * Exposes canonical exact target-cast context frames for target-oriented
--     world-coherent one-step simulation.
--   * Keeps future dispatcher consumers independent of the implementation.
--   * Contains no wrapper relation, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetCastFramesDef
  using (WorldCoherentRightOneStepTargetCastFrames)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetCastFramesProof
  using (world-coherent-right-one-step-target-cast-frames-proofᵀ)


world-coherent-right-one-step-target-cast-framesᵀ :
  WorldCoherentRightOneStepTargetCastFrames
world-coherent-right-one-step-target-cast-framesᵀ =
  world-coherent-right-one-step-target-cast-frames-proofᵀ
