module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingCasesDef
  where

-- File Charter:
--   * Defines the flat semantic leaves for arbitrary-target source
--     function-cast beta scheduling.
--   * Reuses the existing target cast and target `ν` frame capabilities.
--   * Contains no implementation, nested outcome type, postulate, hole, or
--     permissive option.

open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectDef
  using (WorldCoherentSourceFunctionCastBetaDirectᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletDef
  using (WorldCoherentSourceFunctionCastBetaTargetBulletᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using (WorldCoherentSourceOneStepTargetCastFrames)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
  using (WorldCoherentSourceOneStepTargetNuFrames)


record WorldCoherentSourceFunctionCastBetaSchedulingCases : Set₁ where
  field
    sourceFunctionCastBetaDirectCase :
      WorldCoherentSourceFunctionCastBetaDirectᵀ

    sourceFunctionCastBetaTargetBulletCase :
      WorldCoherentSourceFunctionCastBetaTargetBulletᵀ

    sourceFunctionCastBetaTargetCastFrames :
      WorldCoherentSourceOneStepTargetCastFrames

    sourceFunctionCastBetaTargetNuFrames :
      WorldCoherentSourceOneStepTargetNuFrames

open WorldCoherentSourceFunctionCastBetaSchedulingCases public
