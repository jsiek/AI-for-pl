module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingLemma
  where

-- File Charter:
--   * Assembles arbitrary-target source function-cast beta scheduling from
--     the direct target-application leaf.
--   * Supplies target-bullet inversion and all target frames canonically.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using (WorldCoherentSourceFunctionCastBetaRootᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectDef
  using (WorldCoherentSourceFunctionCastBetaDirectᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingCasesLemma
  using (world-coherent-source-function-cast-beta-scheduling-casesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingDispatcherProof
  using
  (world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ)


world-coherent-source-function-cast-beta-schedulingᵀ :
  WorldCoherentSourceFunctionCastBetaDirectᵀ →
  WorldCoherentSourceFunctionCastBetaRootᵀ
world-coherent-source-function-cast-beta-schedulingᵀ direct =
  world-coherent-source-function-cast-beta-scheduling-dispatcher-proofᵀ
    (world-coherent-source-function-cast-beta-scheduling-casesᵀ direct)
