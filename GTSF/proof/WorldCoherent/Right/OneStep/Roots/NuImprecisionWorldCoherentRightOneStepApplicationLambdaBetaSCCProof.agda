module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaSCCProof
  where

-- File Charter:
--   * Closes target ordinary-lambda beta scheduling by structural recursion
--     on the caught source function's inert-cast spine rank.
--   * Uses the ordinary-lambda substitution root at rank zero and the exact
--     four-clause source-function-cast proof at each successor.
--   * Exposes the public unranked value, source-function-value, and
--     function-cast contracts without leaking the private rank.
--   * Contains no postulate, hole, termination pragma, permissive option,
--     catch-all, or compatibility wrapper.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat using
  ( ℕ
  ; suc
  ; zero
  )
open import
  proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef
  using (targetFunctionCastSpineRank)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesDef
  using (WorldCoherentRightOneStepSourceCastFrames)
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesDef
  using (WorldCoherentRightOneStepSourceConversionFrames)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesProof
  using
  (world-coherent-right-one-step-application-lambda-beta-function-cast-values-at-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRankedDef
  using
  ( WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesAtᵀ
  ; WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueAtᵀ
  ; WorldCoherentRightOneStepApplicationLambdaBetaValuesAtᵀ
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRootDef
  using (WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueDef
  using
  ( WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesᵀ
  ; WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueᵀ
  ; WorldCoherentRightOneStepApplicationLambdaBetaValuesᵀ
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueProof
  using
  (world-coherent-right-one-step-application-lambda-beta-source-function-value-at-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaValuesProof
  using
  ( world-coherent-right-one-step-application-lambda-beta-values-at-suc-proofᵀ
  ; world-coherent-right-one-step-application-lambda-beta-values-at-zero-proofᵀ
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


private
  values-at :
    WorldCoherentLeftValueCatchupᵀ →
    WorldCoherentRightOneStepSourceCastFrames →
    WorldCoherentRightOneStepSourceConversionFrames →
    WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ →
    ∀ n →
    WorldCoherentRightOneStepApplicationLambdaBetaValuesAtᵀ n
  values-at catchup cast-frames conversion-frames lambda-root zero =
    world-coherent-right-one-step-application-lambda-beta-values-at-zero-proofᵀ
      lambda-root
  values-at catchup cast-frames conversion-frames lambda-root (suc n) =
    world-coherent-right-one-step-application-lambda-beta-values-at-suc-proofᵀ
      function-cast-at
    where
    lower-values =
      values-at catchup cast-frames conversion-frames lambda-root n

    lower-scheduler :
      WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueAtᵀ n
    lower-scheduler =
      world-coherent-right-one-step-application-lambda-beta-source-function-value-at-proofᵀ
        catchup lower-values

    function-cast-at :
      WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesAtᵀ n
    function-cast-at =
      world-coherent-right-one-step-application-lambda-beta-function-cast-values-at-proofᵀ
        cast-frames conversion-frames lower-scheduler


world-coherent-right-one-step-application-lambda-beta-values-scc-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepSourceCastFrames →
  WorldCoherentRightOneStepSourceConversionFrames →
  WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ →
  WorldCoherentRightOneStepApplicationLambdaBetaValuesᵀ
world-coherent-right-one-step-application-lambda-beta-values-scc-proofᵀ
    catchup cast-frames conversion-frames lambda-root
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ =
  values-at catchup cast-frames conversion-frames lambda-root
    (targetFunctionCastSpineRank vL)
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ refl


world-coherent-right-one-step-application-lambda-beta-source-function-value-scc-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepSourceCastFrames →
  WorldCoherentRightOneStepSourceConversionFrames →
  WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ →
  WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueᵀ
world-coherent-right-one-step-application-lambda-beta-source-function-value-scc-proofᵀ
    catchup cast-frames conversion-frames lambda-root
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ =
  world-coherent-right-one-step-application-lambda-beta-source-function-value-at-proofᵀ
    catchup
    (values-at catchup cast-frames conversion-frames lambda-root
      (targetFunctionCastSpineRank vL))
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ refl


world-coherent-right-one-step-application-lambda-beta-function-cast-values-scc-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepSourceCastFrames →
  WorldCoherentRightOneStepSourceConversionFrames →
  WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ →
  WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesᵀ
world-coherent-right-one-step-application-lambda-beta-function-cast-values-scc-proofᵀ
    catchup cast-frames conversion-frames lambda-root
    coherent exclusive unique wfL okM okM′
    function-related argument-related vV vW vV′ =
  world-coherent-right-one-step-application-lambda-beta-function-cast-values-at-proofᵀ
    cast-frames conversion-frames lower-scheduler
    coherent exclusive unique wfL okM okM′
    function-related argument-related vV vW vV′ refl
  where
  lower-values =
    values-at catchup cast-frames conversion-frames lambda-root
      (targetFunctionCastSpineRank vV)

  lower-scheduler =
    world-coherent-right-one-step-application-lambda-beta-source-function-value-at-proofᵀ
      catchup lower-values
