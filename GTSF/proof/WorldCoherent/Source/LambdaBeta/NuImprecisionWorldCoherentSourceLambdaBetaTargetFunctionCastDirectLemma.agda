module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectLemma
  where

-- File Charter:
--   * Exposes canonical direct target function-cast scheduling from the
--     strictly ranked direct/value SCC proof.
--   * Keeps the private recursion measure out of downstream statements.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastSCCProof
  using
  (world-coherent-source-lambda-beta-target-function-cast-direct-scc-proofᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)


world-coherent-source-lambda-beta-target-function-cast-directᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceSynchronizedLambdaBetaᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ
world-coherent-source-lambda-beta-target-function-cast-directᵀ
    right-catchup synchronized =
  world-coherent-source-lambda-beta-target-function-cast-direct-scc-proofᵀ
    right-catchup synchronized
