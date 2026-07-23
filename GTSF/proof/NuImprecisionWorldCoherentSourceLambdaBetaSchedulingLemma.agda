module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingLemma
  where

-- File Charter:
--   * Assembles arbitrary-target ordinary lambda-beta scheduling.
--   * Leaves only right-value catch-up as an explicit dependency;
--     synchronized beta and target-bullet inversion are canonical.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectLemma
  using (world-coherent-source-lambda-beta-directᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingDef
  using (WorldCoherentSourceLambdaBetaSchedulingᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingProof
  using (world-coherent-source-lambda-beta-scheduling-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletLemma
  using (world-coherent-source-lambda-beta-target-bulletᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesLemma
  using (world-coherent-source-one-step-target-cast-frames)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesLemma
  using (world-coherent-source-one-step-target-nu-framesᵀ)


world-coherent-source-lambda-beta-schedulingᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceLambdaBetaSchedulingᵀ
world-coherent-source-lambda-beta-schedulingᵀ
    right-catchup =
  world-coherent-source-lambda-beta-scheduling-proofᵀ
    (world-coherent-source-lambda-beta-directᵀ right-catchup)
    world-coherent-source-lambda-beta-target-bulletᵀ
    world-coherent-source-one-step-target-cast-frames
    world-coherent-source-one-step-target-nu-framesᵀ
