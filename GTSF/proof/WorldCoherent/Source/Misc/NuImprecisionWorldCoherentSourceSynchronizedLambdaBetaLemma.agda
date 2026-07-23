module
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaLemma
  where

-- File Charter:
--   * Assembles synchronized ordinary-lambda beta from canonical parallel
--     substitution.
--   * Instantiates parallel substitution to single substitution, then invokes
--     the checked synchronized-beta proof.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionLemma using
  (quotiented-parallel-term-substitution-lemmaᵀ)
open import proof.Substitution.Term.NuImprecisionSingleSubstitutionEnvironmentLemma using
  (quotiented-single-substitution-environment-lemmaᵀ)
open import proof.Substitution.Term.NuImprecisionTermSubstitutionProof using
  (quotiented-term-substitution-proofᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaProof
  using (world-coherent-source-synchronized-lambda-beta-proofᵀ)


world-coherent-source-synchronized-lambda-beta-lemmaᵀ :
  WorldCoherentSourceSynchronizedLambdaBetaᵀ
world-coherent-source-synchronized-lambda-beta-lemmaᵀ =
  world-coherent-source-synchronized-lambda-beta-proofᵀ
    (quotiented-term-substitution-proofᵀ
      quotiented-parallel-term-substitution-lemmaᵀ
      quotiented-single-substitution-environment-lemmaᵀ)
