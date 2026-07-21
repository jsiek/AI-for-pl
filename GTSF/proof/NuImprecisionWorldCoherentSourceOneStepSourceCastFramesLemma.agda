module
  proof.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesLemma
  where

-- File Charter:
--   * Supplies the canonical exact-result source cast/conversion frames.
--   * Keeps the recursive outcome split outside this related-branch leaf.
--   * Contains no postulate, hole, permissive option, or dispatcher import.

open import
  proof.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesDef
  using (WorldCoherentSourceOneStepSourceCastFrames)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesProof
  using (world-coherent-source-one-step-source-cast-frames-proofᵀ)


world-coherent-source-one-step-source-cast-framesᵀ :
  WorldCoherentSourceOneStepSourceCastFrames
world-coherent-source-one-step-source-cast-framesᵀ =
  world-coherent-source-one-step-source-cast-frames-proofᵀ
