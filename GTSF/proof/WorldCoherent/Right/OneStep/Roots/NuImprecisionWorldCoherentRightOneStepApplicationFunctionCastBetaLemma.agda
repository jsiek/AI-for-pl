module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaLemma
  where

-- File Charter:
--   * Exposes canonical target function-cast beta scheduling for arbitrary
--     source functions and for the two caught-value boundaries.
--   * Supplies canonical source cast and conversion frames, paired terminals,
--     and source-lambda terminals.
--   * Leaves world-coherent source-to-value catch-up as the sole explicit
--     scheduling dependency.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

open import
  proof.Quotient.NuImprecisionQuotientFunctionPairedNarrowingApplicationLemma
  using (quotient-function-paired-narrowing-applicationᵀ)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationLemma
  using (source-function-cast-beta-paired-quotient-relationᵀ)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationLemma
  using
  (source-function-cast-beta-paired-widening-function-compatible-relationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesLemma
  using (world-coherent-right-one-step-source-cast-framesᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesLemma
  using (world-coherent-right-one-step-source-conversion-framesᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaDef
  using
  ( WorldCoherentRightOneStepApplicationFunctionCastBetaᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaValuesᵀ
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesProof
  using
  (world-coherent-right-one-step-application-function-cast-beta-lambda-values-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedProof
  using
  (world-coherent-right-one-step-application-function-cast-beta-paired-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaSCCProof
  using
  ( world-coherent-right-one-step-application-function-cast-beta-scc-proofᵀ
  ; world-coherent-right-one-step-application-function-cast-beta-source-function-value-scc-proofᵀ
  ; world-coherent-right-one-step-application-function-cast-beta-values-scc-proofᵀ
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-application-function-cast-beta-valuesᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationFunctionCastBetaValuesᵀ
world-coherent-right-one-step-application-function-cast-beta-valuesᵀ catchup =
  world-coherent-right-one-step-application-function-cast-beta-values-scc-proofᵀ
    catchup
    world-coherent-right-one-step-source-cast-framesᵀ
    world-coherent-right-one-step-source-conversion-framesᵀ
    (world-coherent-right-one-step-application-function-cast-beta-paired-proofᵀ
      source-function-cast-beta-paired-widening-function-compatible-relationᵀ
      (source-function-cast-beta-paired-quotient-relationᵀ
        quotient-function-paired-narrowing-applicationᵀ))
    world-coherent-right-one-step-application-function-cast-beta-lambda-values-proofᵀ


world-coherent-right-one-step-application-function-cast-beta-source-function-valueᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueᵀ
world-coherent-right-one-step-application-function-cast-beta-source-function-valueᵀ
    catchup =
  world-coherent-right-one-step-application-function-cast-beta-source-function-value-scc-proofᵀ
    catchup
    world-coherent-right-one-step-source-cast-framesᵀ
    world-coherent-right-one-step-source-conversion-framesᵀ
    (world-coherent-right-one-step-application-function-cast-beta-paired-proofᵀ
      source-function-cast-beta-paired-widening-function-compatible-relationᵀ
      (source-function-cast-beta-paired-quotient-relationᵀ
        quotient-function-paired-narrowing-applicationᵀ))
    world-coherent-right-one-step-application-function-cast-beta-lambda-values-proofᵀ


world-coherent-right-one-step-application-function-cast-betaᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationFunctionCastBetaᵀ
world-coherent-right-one-step-application-function-cast-betaᵀ catchup =
  world-coherent-right-one-step-application-function-cast-beta-scc-proofᵀ
    catchup
    world-coherent-right-one-step-source-cast-framesᵀ
    world-coherent-right-one-step-source-conversion-framesᵀ
    (world-coherent-right-one-step-application-function-cast-beta-paired-proofᵀ
      source-function-cast-beta-paired-widening-function-compatible-relationᵀ
      (source-function-cast-beta-paired-quotient-relationᵀ
        quotient-function-paired-narrowing-applicationᵀ))
    world-coherent-right-one-step-application-function-cast-beta-lambda-values-proofᵀ
