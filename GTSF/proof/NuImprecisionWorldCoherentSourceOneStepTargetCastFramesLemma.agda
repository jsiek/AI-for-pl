module
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesLemma
  where

-- File Charter:
--   * Supplies the canonical source-step target cast/conversion frames.
--   * Keeps the structural primitive dispatcher independent of the Ginger
--     implementation module.
--   * Contains no postulate, hole, permissive option, or dispatcher import.

open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using (WorldCoherentSourceOneStepTargetCastFrames)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesProof
  using (world-coherent-source-one-step-target-cast-frames-proofᵀ)


world-coherent-source-one-step-target-cast-frames :
  WorldCoherentSourceOneStepTargetCastFrames
world-coherent-source-one-step-target-cast-frames =
  world-coherent-source-one-step-target-cast-frames-proofᵀ
