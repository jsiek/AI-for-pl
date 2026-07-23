module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletLemma
  where

-- File Charter:
--   * Exposes the strict target-bullet lambda-beta inversion proof through the
--     canonical theorem name.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletDef
  using (WorldCoherentSourceLambdaBetaTargetBulletᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletProof
  using (world-coherent-source-lambda-beta-target-bullet-proofᵀ)


world-coherent-source-lambda-beta-target-bulletᵀ :
  WorldCoherentSourceLambdaBetaTargetBulletᵀ
world-coherent-source-lambda-beta-target-bulletᵀ =
  world-coherent-source-lambda-beta-target-bullet-proofᵀ
