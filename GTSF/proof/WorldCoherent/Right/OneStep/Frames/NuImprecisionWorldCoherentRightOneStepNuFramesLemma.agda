module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepNuFramesLemma
  where

-- File Charter:
--   * Exposes the canonical exact matched, source-only, and target-only
--     ordinary/casted ν frames for target-oriented one-step simulation.
--   * Keeps dispatcher consumers independent of the implementation module.
--   * Contains no compatibility alias, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepNuFramesDef
  using (WorldCoherentRightOneStepNuFrames)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepNuFramesProof
  using (world-coherent-right-one-step-nu-frames-proofᵀ)


world-coherent-right-one-step-nu-framesᵀ :
  WorldCoherentRightOneStepNuFrames
world-coherent-right-one-step-nu-framesᵀ =
  world-coherent-right-one-step-nu-frames-proofᵀ
