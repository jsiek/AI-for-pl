module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastValueLemma
  where

-- File Charter:
--   * Exposes canonical target function-cast value scheduling from the
--     strictly ranked direct/value SCC proof.
--   * Keeps the private recursion measure out of downstream statements.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastValueDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastSCCProof
  using
  (world-coherent-source-lambda-beta-target-function-cast-value-scc-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)


world-coherent-source-lambda-beta-target-function-cast-valueᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceSynchronizedLambdaBetaᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ
world-coherent-source-lambda-beta-target-function-cast-valueᵀ
    right-catchup synchronized =
  world-coherent-source-lambda-beta-target-function-cast-value-scc-proofᵀ
    right-catchup synchronized
