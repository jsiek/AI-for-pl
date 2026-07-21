module
  proof.NuImprecisionWorldCoherentSourceOneStepBinaryFramesLemma
  where

-- File Charter:
--   * Exposes the canonical exact application and primitive source-step
--     frames.
--   * Keeps consumers independent of the Ginger implementation module.
--   * Contains no result wrapper, postulate, hole, permissive option, or
--     compatibility alias.

open import
  proof.NuImprecisionWorldCoherentSourceOneStepBinaryFramesDef
  using (WorldCoherentSourceOneStepBinaryFrames)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepBinaryFramesProof
  using (world-coherent-source-one-step-binary-frames-proofᵀ)


world-coherent-source-one-step-binary-framesᵀ :
  WorldCoherentSourceOneStepBinaryFrames
world-coherent-source-one-step-binary-framesᵀ =
  world-coherent-source-one-step-binary-frames-proofᵀ
