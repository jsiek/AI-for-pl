module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletLemma
  where

-- File Charter:
--   * Exposes the canonical source function-cast beta target-bullet proof.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletDef
  using (WorldCoherentSourceFunctionCastBetaTargetBulletᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletProof
  using (world-coherent-source-function-cast-beta-target-bullet-proofᵀ)


world-coherent-source-function-cast-beta-target-bulletᵀ :
  WorldCoherentSourceFunctionCastBetaTargetBulletᵀ
world-coherent-source-function-cast-beta-target-bulletᵀ =
  world-coherent-source-function-cast-beta-target-bullet-proofᵀ
