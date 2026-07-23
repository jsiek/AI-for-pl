module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingCasesDef
  where

-- File Charter:
--   * Defines the two dependencies of ordinary lambda-beta scheduling.
--   * Separates direct application scheduling from structural target frames.
--   * Contains no dispatcher, implementation, postulate, hole, or option.

open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaDirectDef
  using (WorldCoherentSourceLambdaBetaDirectᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using (WorldCoherentSourceOneStepTargetCastFrames)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletDef
  using (WorldCoherentSourceLambdaBetaTargetBulletᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
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
