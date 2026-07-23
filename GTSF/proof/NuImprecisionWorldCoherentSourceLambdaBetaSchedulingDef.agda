module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingDef
  where

-- File Charter:
--   * States target scheduling for the ordinary source lambda-beta root.
--   * Takes synchronized lambda beta as its only proof dependency and returns
--     the existing arbitrary-target application root directly.
--   * Introduces no result/view carrier, implementation, postulate, hole, or
--     permissive option.

open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using (WorldCoherentSourceLambdaBetaRootᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)


WorldCoherentSourceLambdaBetaSchedulingᵀ : Set₁
WorldCoherentSourceLambdaBetaSchedulingᵀ =
  WorldCoherentSourceSynchronizedLambdaBetaᵀ →
  WorldCoherentSourceLambdaBetaRootᵀ
