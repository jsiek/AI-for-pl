module
  proof.NuImprecisionWorldCoherentSourceOneStepSourceNuFramesLemma
  where

-- File Charter:
--   * Exposes the canonical matched and source-only source-ν step frames.
--   * Keeps consumers independent of the Ginger implementation module.
--   * Contains no wrapper result, postulate, hole, permissive option, or
--     compatibility alias.

open import
  proof.NuImprecisionWorldCoherentSourceOneStepSourceNuFramesDef
  using (WorldCoherentSourceOneStepSourceNuFrames)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepSourceNuFramesProof
  using (world-coherent-source-one-step-source-nu-frames-proofᵀ)


world-coherent-source-one-step-source-nu-framesᵀ :
  WorldCoherentSourceOneStepSourceNuFrames
world-coherent-source-one-step-source-nu-framesᵀ =
  world-coherent-source-one-step-source-nu-frames-proofᵀ
