module
  proof.WorldCoherent.Source.FunctionCastBeta.Scheduling.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingCasesLemma
  where

-- File Charter:
--   * Assembles source function-cast beta scheduling cases from the direct
--     target-application leaf and canonical target structural cases.
--   * Leaves only direct target-application scheduling explicit.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Source.FunctionCastBeta.Direct.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectDef
  using (WorldCoherentSourceFunctionCastBetaDirectᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.Scheduling.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingCasesDef
  using (WorldCoherentSourceFunctionCastBetaSchedulingCases)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletLemma
  using (world-coherent-source-function-cast-beta-target-bulletᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesLemma
  using (world-coherent-source-one-step-target-cast-frames)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesLemma
  using (world-coherent-source-one-step-target-nu-framesᵀ)


world-coherent-source-function-cast-beta-scheduling-casesᵀ :
  WorldCoherentSourceFunctionCastBetaDirectᵀ →
  WorldCoherentSourceFunctionCastBetaSchedulingCases
world-coherent-source-function-cast-beta-scheduling-casesᵀ direct =
  record
    { sourceFunctionCastBetaDirectCase = direct
    ; sourceFunctionCastBetaTargetBulletCase =
        world-coherent-source-function-cast-beta-target-bulletᵀ
    ; sourceFunctionCastBetaTargetCastFrames =
        world-coherent-source-one-step-target-cast-frames
    ; sourceFunctionCastBetaTargetNuFrames =
        world-coherent-source-one-step-target-nu-framesᵀ
    }
