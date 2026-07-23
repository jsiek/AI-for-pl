module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingCasesDef
  where

-- File Charter:
--   * Defines the two dependencies of ordinary lambda-beta scheduling.
--   * Separates direct application scheduling from structural target frames.
--   * Contains no dispatcher, implementation, postulate, hole, or option.

open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectDef
  using (WorldCoherentSourceLambdaBetaDirectᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using (WorldCoherentSourceOneStepTargetCastFrames)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletDef
  using (WorldCoherentSourceLambdaBetaTargetBulletᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
  using (WorldCoherentSourceOneStepTargetNuFrames)


record WorldCoherentSourceLambdaBetaSchedulingCases : Set₁ where
  field
    sourceLambdaBetaDirectCase :
      WorldCoherentSourceLambdaBetaDirectᵀ

    sourceLambdaBetaTargetBulletCase :
      WorldCoherentSourceLambdaBetaTargetBulletᵀ

    sourceLambdaBetaTargetCastFrames :
      WorldCoherentSourceOneStepTargetCastFrames

    sourceLambdaBetaTargetNuFrames :
      WorldCoherentSourceOneStepTargetNuFrames

open WorldCoherentSourceLambdaBetaSchedulingCases public
