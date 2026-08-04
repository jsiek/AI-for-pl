module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesLemma
  where

-- File Charter:
--   * Supplies the canonical exact-result source cast/conversion frames.
--   * Keeps the recursive outcome split outside this related-branch leaf.
--   * Contains no postulate, hole, permissive option, or dispatcher import.

open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesDef
  using (WorldCoherentSourceOneStepSourceCastFrames)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesProof
  using (world-coherent-source-one-step-source-cast-frames-proofᵀ)


world-coherent-source-one-step-source-cast-framesᵀ :
  WorldCoherentSourceOneStepSourceCastFrames
world-coherent-source-one-step-source-cast-framesᵀ =
  world-coherent-source-one-step-source-cast-frames-proofᵀ
