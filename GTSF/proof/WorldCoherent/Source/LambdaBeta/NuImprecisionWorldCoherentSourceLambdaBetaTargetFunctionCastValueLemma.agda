module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastValueLemma
  where

-- File Charter:
--   * Exposes canonical target function-cast value scheduling from the
--     strictly ranked direct/value SCC proof.
--   * Keeps the private recursion measure out of downstream statements.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastValueDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastSCCProof
  using
  (world-coherent-source-lambda-beta-target-function-cast-value-scc-proofᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)


world-coherent-source-lambda-beta-target-function-cast-valueᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceSynchronizedLambdaBetaᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ
world-coherent-source-lambda-beta-target-function-cast-valueᵀ
    right-catchup synchronized =
  world-coherent-source-lambda-beta-target-function-cast-value-scc-proofᵀ
    right-catchup synchronized
