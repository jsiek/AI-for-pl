module
  proof.WorldCoherent.Source.FunctionCastBeta.Scheduling.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingLemma
  where

-- File Charter:
--   * Assembles arbitrary-target source function-cast beta scheduling from
--     the direct target-application leaf.
--   * Supplies target-bullet inversion and all target frames canonically.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using (WorldCoherentSourceFunctionCastBetaRootᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.Direct.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectDef
  using (WorldCoherentSourceFunctionCastBetaDirectᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.Scheduling.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingCasesLemma
  using (world-coherent-source-function-cast-beta-scheduling-casesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.Scheduling.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingDispatcherProof
  using
  (world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ)


world-coherent-source-function-cast-beta-schedulingᵀ :
  WorldCoherentSourceFunctionCastBetaDirectᵀ →
  WorldCoherentSourceFunctionCastBetaRootᵀ
world-coherent-source-function-cast-beta-schedulingᵀ direct =
  world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    (world-coherent-source-function-cast-beta-scheduling-casesᵀ direct)
