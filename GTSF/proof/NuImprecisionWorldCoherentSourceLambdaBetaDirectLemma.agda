module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectLemma
  where

-- File Charter:
--   * Assembles direct ordinary lambda-beta scheduling from right-value
--     catch-up and the completed ranked function-cast scheduler.
--   * Builds the target-lambda terminal from synchronized beta canonically.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import proof.NuImprecisionSourceSilentCompositionLemma using
  (source-silent-compositionᵀ)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectCasesDef
  using (WorldCoherentSourceLambdaBetaDirectCases)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectDef
  using (WorldCoherentSourceLambdaBetaDirectᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaDirectProof
  using (world-coherent-source-lambda-beta-direct-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectLemma
  using
  (world-coherent-source-lambda-beta-target-function-cast-directᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetLambdaDirectProof
  using
  (world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSilentCompositionLemma
  using (world-coherent-source-silent-compositionᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
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
