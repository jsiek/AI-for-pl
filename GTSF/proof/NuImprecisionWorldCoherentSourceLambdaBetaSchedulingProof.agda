module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingProof
  where

-- File Charter:
--   * Assembles ordinary lambda-beta target scheduling from its flat leaves.
--   * Instantiates direct scheduling with synchronized beta, then supplies
--     target-bullet, target-cast, and target-ν structural cases.
--   * Contains no leaf implementation, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectDef
  using (WorldCoherentSourceLambdaBetaDirectᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingCasesDef
  using (WorldCoherentSourceLambdaBetaSchedulingCases)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingDef
  using (WorldCoherentSourceLambdaBetaSchedulingᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingDispatcherProof
  using
  (world-coherent-source-lambda-beta-scheduling-dispatcher-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletDef
  using (WorldCoherentSourceLambdaBetaTargetBulletᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using (WorldCoherentSourceOneStepTargetCastFrames)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
  using (WorldCoherentSourceOneStepTargetNuFrames)
open import
  proof.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)


world-coherent-source-lambda-beta-scheduling-proofᵀ :
  (WorldCoherentSourceSynchronizedLambdaBetaᵀ →
    WorldCoherentSourceLambdaBetaDirectᵀ) →
  WorldCoherentSourceLambdaBetaTargetBulletᵀ →
  WorldCoherentSourceOneStepTargetCastFrames →
  WorldCoherentSourceOneStepTargetNuFrames →
  WorldCoherentSourceLambdaBetaSchedulingᵀ
world-coherent-source-lambda-beta-scheduling-proofᵀ
    direct target-bullet target-casts target-νs synchronized =
  world-coherent-source-lambda-beta-scheduling-dispatcher-proofᵀ cases
  where
  cases : WorldCoherentSourceLambdaBetaSchedulingCases
  cases = record
    { sourceLambdaBetaDirectCase = direct synchronized
    ; sourceLambdaBetaTargetBulletCase = target-bullet
    ; sourceLambdaBetaTargetCastFrames = target-casts
    ; sourceLambdaBetaTargetNuFrames = target-νs
    }
