module
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetLambdaValuesLemma
  where

-- File Charter:
--   * Exposes the canonical target-lambda value/value terminal.
--   * Keeps the statement, structural proof, and assembly separate.
--   * Contains no postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetLambdaValuesDef
  using (WorldCoherentSourceFunctionCastBetaTargetLambdaValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetLambdaValuesProof
  using
  (world-coherent-source-function-cast-beta-target-lambda-values-proofᵀ)


world-coherent-source-function-cast-beta-target-lambda-valuesᵀ :
  WorldCoherentSourceFunctionCastBetaTargetLambdaValuesᵀ
world-coherent-source-function-cast-beta-target-lambda-valuesᵀ =
  world-coherent-source-function-cast-beta-target-lambda-values-proofᵀ
