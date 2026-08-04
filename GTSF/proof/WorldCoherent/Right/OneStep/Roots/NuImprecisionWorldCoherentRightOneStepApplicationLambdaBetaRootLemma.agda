module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRootLemma
  where

-- File Charter:
--   * Exposes the canonical target-oriented ordinary-lambda beta root.
--   * Supplies the completed quotiented term-substitution theorem.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

open import
  proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionLemma
  using (quotiented-parallel-term-substitution-lemmaᵀ)
open import
  proof.Substitution.Term.NuImprecisionSingleSubstitutionEnvironmentLemma
  using (quotiented-single-substitution-environment-lemmaᵀ)
open import
  proof.Substitution.Term.NuImprecisionTermSubstitutionProof
  using (quotiented-term-substitution-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRootDef
  using (WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRootProof
  using
  (world-coherent-right-one-step-application-lambda-beta-root-proofᵀ)


world-coherent-right-one-step-application-lambda-beta-rootᵀ :
  WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ
world-coherent-right-one-step-application-lambda-beta-rootᵀ =
  world-coherent-right-one-step-application-lambda-beta-root-proofᵀ
    (quotiented-term-substitution-proofᵀ
      quotiented-parallel-term-substitution-lemmaᵀ
      quotiented-single-substitution-environment-lemmaᵀ)
