module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaDirectCasesDef
  where

-- File Charter:
--   * Defines the two terminal target-function shapes reached by direct
--     ordinary lambda-beta scheduling.
--   * Reuses the existing canonical arrow-value classification and introduces
--     no result or view carrier.
--   * Contains no dispatcher, implementation, postulate, hole, or option.

open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetLambdaDirectDef
  using (WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ)


record WorldCoherentSourceLambdaBetaDirectCases : Set₁ where
  field
    sourceLambdaBetaTargetLambdaDirectCase :
      WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ

    sourceLambdaBetaTargetFunctionCastDirectCase :
      WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ

open WorldCoherentSourceLambdaBetaDirectCases public
