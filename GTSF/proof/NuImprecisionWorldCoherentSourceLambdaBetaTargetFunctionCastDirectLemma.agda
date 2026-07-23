module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectLemma
  where

-- File Charter:
--   * Exposes canonical direct target function-cast scheduling from the
--     strictly ranked direct/value SCC proof.
--   * Keeps the private recursion measure out of downstream statements.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastSCCProof
  using
  (world-coherent-source-lambda-beta-target-function-cast-direct-scc-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)


world-coherent-source-lambda-beta-target-function-cast-directᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceSynchronizedLambdaBetaᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ
world-coherent-source-lambda-beta-target-function-cast-directᵀ
    right-catchup synchronized =
  world-coherent-source-lambda-beta-target-function-cast-direct-scc-proofᵀ
    right-catchup synchronized
