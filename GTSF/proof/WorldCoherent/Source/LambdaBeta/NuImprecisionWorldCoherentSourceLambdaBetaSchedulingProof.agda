module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingProof
  where

-- File Charter:
--   * Assembles ordinary lambda-beta target scheduling from its flat leaves.
--   * Instantiates direct scheduling with synchronized beta, then supplies
--     target-bullet, target-cast, and target-ν structural cases.
--   * Contains no leaf implementation, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaDirectDef
  using (WorldCoherentSourceLambdaBetaDirectᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingCasesDef
  using (WorldCoherentSourceLambdaBetaSchedulingCases)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingDef
  using (WorldCoherentSourceLambdaBetaSchedulingᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingDispatcherProof
  using
  (world-coherent-source-lambda-beta-scheduling-dispatcher-proofᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletDef
  using (WorldCoherentSourceLambdaBetaTargetBulletᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using (WorldCoherentSourceOneStepTargetCastFrames)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
  using (WorldCoherentSourceOneStepTargetNuFrames)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
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
