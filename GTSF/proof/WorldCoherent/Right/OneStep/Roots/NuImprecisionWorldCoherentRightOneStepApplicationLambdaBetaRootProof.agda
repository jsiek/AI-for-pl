module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRootProof
  where

-- File Charter:
--   * Proves the target-oriented ordinary-lambda beta root from quotiented
--     substitution.
--   * Takes one source beta step, leaves the already-reduced target body
--     unchanged, and preserves the current coherent world.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     or compatibility wrapper.

open import NuReduction using
  ( β
  ; pure-step
  )
open import QuotientedTermImprecision using (prefix-reflⁱ)
open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  ( weak-one-step-keep-source-catchup-type-coherenceᵀ
  ; weak-one-step-keep-source-catchup-transportᵀ
  ; weak-one-step-keep-source-catchupᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using (weak-indexed-result)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.Substitution.Term.NuImprecisionTermSubstitutionDef
  using (QuotientedTermSubstitutionᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (world-indexed-outcome-related)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRootDef
  using (WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ)


world-coherent-right-one-step-application-lambda-beta-root-proofᵀ :
  QuotientedTermSubstitutionᵀ →
  WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ
world-coherent-right-one-step-application-lambda-beta-root-proofᵀ
    substitute
    {ρ = ρ}
    coherent exclusive unique
    vV noV vV′ noV′ noN noN′ body argument =
  world-indexed-outcome-related
    indexed lineage coherent exclusive unique
  where
  post-beta =
    substitute unique noN noN′ noV noV′ body argument

  source→ = pure-step (β vV)

  raw =
    weak-one-step-keep-source-catchupᵀ source→ post-beta

  indexed =
    weak-indexed-result raw post-beta
      (weak-one-step-keep-source-catchup-transportᵀ
        source→ post-beta)
      (weak-one-step-keep-source-catchup-type-coherenceᵀ
        source→ post-beta)

  lineage =
    weak-step-store-lineage
      ρ rel-store-embedding-reflⁱ prefix-reflⁱ
