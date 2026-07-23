module
  proof.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaLemma
  where

-- File Charter:
--   * Assembles synchronized ordinary-lambda beta from canonical parallel
--     substitution.
--   * Instantiates parallel substitution to single substitution, then invokes
--     the checked synchronized-beta proof.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import proof.NuImprecisionParallelTermSubstitutionLemma using
  (quotiented-parallel-term-substitution-lemmaᵀ)
open import proof.NuImprecisionSingleSubstitutionEnvironmentLemma using
  (quotiented-single-substitution-environment-lemmaᵀ)
open import proof.NuImprecisionTermSubstitutionProof using
  (quotiented-term-substitution-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaProof
  using (world-coherent-source-synchronized-lambda-beta-proofᵀ)


world-coherent-source-synchronized-lambda-beta-lemmaᵀ :
  WorldCoherentSourceSynchronizedLambdaBetaᵀ
world-coherent-source-synchronized-lambda-beta-lemmaᵀ =
  world-coherent-source-synchronized-lambda-beta-proofᵀ
    (quotiented-term-substitution-proofᵀ
      quotiented-parallel-term-substitution-lemmaᵀ
      quotiented-single-substitution-environment-lemmaᵀ)
