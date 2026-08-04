module proof.Source.OneStep.NuImprecisionSourceOneStepDeltaRootLemma where

-- File Charter:
--   * Supplies the canonical synchronized source delta root from its proof.
--   * Keeps primitive-root callers independent of the Ginger worker module.
--   * Contains no postulate, hole, permissive option, or simulation import.

open import proof.Source.OneStep.NuImprecisionSourceOneStepDeltaRootDef using
  (WorldCoherentSourceDeltaRootᵀ)
open import proof.Source.OneStep.NuImprecisionSourceOneStepDeltaRootProof using
  (world-coherent-source-delta-root-proofᵀ)


world-coherent-source-delta-rootᵀ :
  WorldCoherentSourceDeltaRootᵀ
world-coherent-source-delta-rootᵀ =
  world-coherent-source-delta-root-proofᵀ
