module
  proof.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesLemma
  where

-- File Charter:
--   * Exposes the canonical ordinary and casted target-ν source-step frames.
--   * Keeps consumers independent of the Ginger implementation module.
--   * Contains no wrapper result, postulate, hole, permissive option, or
--     compatibility alias.

open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
  using (WorldCoherentSourceOneStepTargetNuFrames)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesProof
  using (world-coherent-source-one-step-target-nu-frames-proofᵀ)


world-coherent-source-one-step-target-nu-framesᵀ :
  WorldCoherentSourceOneStepTargetNuFrames
world-coherent-source-one-step-target-nu-framesᵀ =
  world-coherent-source-one-step-target-nu-frames-proofᵀ
