module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaDirectLemma
  where

-- File Charter:
--   * Assembles direct ordinary lambda-beta scheduling from right-value
--     catch-up and the completed ranked function-cast scheduler.
--   * Builds the target-lambda terminal from synchronized beta canonically.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import proof.Source.Core.NuImprecisionSourceSilentCompositionLemma using
  (source-silent-compositionᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaDirectCasesDef
  using (WorldCoherentSourceLambdaBetaDirectCases)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaDirectDef
  using (WorldCoherentSourceLambdaBetaDirectᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaDirectProof
  using (world-coherent-source-lambda-beta-direct-proofᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectLemma
  using
  (world-coherent-source-lambda-beta-target-function-cast-directᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetLambdaDirectProof
  using
  (world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ)
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceSilentCompositionLemma
  using (world-coherent-source-silent-compositionᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)


world-coherent-source-lambda-beta-directᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceSynchronizedLambdaBetaᵀ →
  WorldCoherentSourceLambdaBetaDirectᵀ
world-coherent-source-lambda-beta-directᵀ
    right-catchup synchronized =
  world-coherent-source-lambda-beta-direct-proofᵀ
    right-catchup world-coherent-source-silent-compositionᵀ cases
  where
  cases : WorldCoherentSourceLambdaBetaDirectCases
  cases = record
    { sourceLambdaBetaTargetLambdaDirectCase =
        world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ
          right-catchup source-silent-compositionᵀ synchronized
    ; sourceLambdaBetaTargetFunctionCastDirectCase =
        world-coherent-source-lambda-beta-target-function-cast-directᵀ
          right-catchup synchronized
    }
