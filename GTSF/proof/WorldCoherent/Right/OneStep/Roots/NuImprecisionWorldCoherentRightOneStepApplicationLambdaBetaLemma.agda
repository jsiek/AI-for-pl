module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaLemma
  where

-- File Charter:
--   * Exposes target ordinary-lambda beta scheduling for related source
--     values, caught source function values, and source function casts.
--   * Supplies the canonical source cast frames, source conversion frames,
--     and direct ordinary-lambda substitution root.
--   * Leaves world-coherent source-to-value catch-up as the sole explicit
--     scheduling dependency.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesLemma
  using (world-coherent-right-one-step-source-cast-framesᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesLemma
  using (world-coherent-right-one-step-source-conversion-framesᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaProof
  using (world-coherent-right-one-step-application-lambda-beta-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRootLemma
  using (world-coherent-right-one-step-application-lambda-beta-rootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaSCCProof
  using
  ( world-coherent-right-one-step-application-lambda-beta-function-cast-values-scc-proofᵀ
  ; world-coherent-right-one-step-application-lambda-beta-source-function-value-scc-proofᵀ
  ; world-coherent-right-one-step-application-lambda-beta-values-scc-proofᵀ
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueDef
  using
  ( WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesᵀ
  ; WorldCoherentRightOneStepApplicationLambdaBetaᵀ
  ; WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueᵀ
  ; WorldCoherentRightOneStepApplicationLambdaBetaValuesᵀ
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-application-lambda-beta-valuesᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationLambdaBetaValuesᵀ
world-coherent-right-one-step-application-lambda-beta-valuesᵀ catchup =
  world-coherent-right-one-step-application-lambda-beta-values-scc-proofᵀ
    catchup
    world-coherent-right-one-step-source-cast-framesᵀ
    world-coherent-right-one-step-source-conversion-framesᵀ
    world-coherent-right-one-step-application-lambda-beta-rootᵀ


world-coherent-right-one-step-application-lambda-beta-source-function-valueᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueᵀ
world-coherent-right-one-step-application-lambda-beta-source-function-valueᵀ
    catchup =
  world-coherent-right-one-step-application-lambda-beta-source-function-value-scc-proofᵀ
    catchup
    world-coherent-right-one-step-source-cast-framesᵀ
    world-coherent-right-one-step-source-conversion-framesᵀ
    world-coherent-right-one-step-application-lambda-beta-rootᵀ


world-coherent-right-one-step-application-lambda-beta-function-cast-valuesᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesᵀ
world-coherent-right-one-step-application-lambda-beta-function-cast-valuesᵀ
    catchup =
  world-coherent-right-one-step-application-lambda-beta-function-cast-values-scc-proofᵀ
    catchup
    world-coherent-right-one-step-source-cast-framesᵀ
    world-coherent-right-one-step-source-conversion-framesᵀ
    world-coherent-right-one-step-application-lambda-beta-rootᵀ


world-coherent-right-one-step-application-lambda-betaᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationLambdaBetaᵀ
world-coherent-right-one-step-application-lambda-betaᵀ catchup =
  world-coherent-right-one-step-application-lambda-beta-proofᵀ
    catchup
    (world-coherent-right-one-step-application-lambda-beta-source-function-valueᵀ
      catchup)
