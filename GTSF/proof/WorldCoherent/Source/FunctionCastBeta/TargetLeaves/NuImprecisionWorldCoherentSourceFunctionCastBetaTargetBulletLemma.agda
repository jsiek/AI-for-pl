module
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletLemma
  where

-- File Charter:
--   * Exposes the canonical source function-cast beta target-bullet proof.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletDef
  using (WorldCoherentSourceFunctionCastBetaTargetBulletᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletProof
  using (world-coherent-source-function-cast-beta-target-bullet-proofᵀ)


world-coherent-source-function-cast-beta-target-bulletᵀ :
  WorldCoherentSourceFunctionCastBetaTargetBulletᵀ
world-coherent-source-function-cast-beta-target-bulletᵀ =
  world-coherent-source-function-cast-beta-target-bullet-proofᵀ
