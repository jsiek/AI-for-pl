module proof.Source.OneStep.NuImprecisionSourceOneStepBlameRootLemma where

-- File Charter:
--   * Supplies the canonical source keep-step blame root from its strict proof.
--   * Keeps source-root callers independent of the Ginger worker module.
--   * Contains no postulate, hole, permissive option, or simulation import.

open import proof.Source.OneStep.NuImprecisionSourceOneStepBlameRootDef using
  (WorldCoherentSourceKeepBlameRootᵀ)
open import proof.Source.OneStep.NuImprecisionSourceOneStepBlameRootProof using
  (world-coherent-source-keep-blame-root-proofᵀ)


world-coherent-source-keep-blame-rootᵀ :
  WorldCoherentSourceKeepBlameRootᵀ
world-coherent-source-keep-blame-rootᵀ =
  world-coherent-source-keep-blame-root-proofᵀ
