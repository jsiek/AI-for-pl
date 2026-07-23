module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetLambdaDirectLemma
  where

-- File Charter:
--   * Assembles the target-lambda direct terminal from canonical synchronized
--     beta and source-silent composition.
--   * Exposes only the unfinished right-value catch-up dependency.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import proof.Source.Core.NuImprecisionSourceSilentCompositionLemma using
  (source-silent-compositionᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetLambdaDirectDef
  using (WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetLambdaDirectProof
  using
  (world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaLemma
  using (world-coherent-source-synchronized-lambda-beta-lemmaᵀ)


world-coherent-source-lambda-beta-target-lambda-directᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceLambdaBetaTargetLambdaDirectᵀ
world-coherent-source-lambda-beta-target-lambda-directᵀ right-catchup =
  world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ
    right-catchup source-silent-compositionᵀ
    world-coherent-source-synchronized-lambda-beta-lemmaᵀ
