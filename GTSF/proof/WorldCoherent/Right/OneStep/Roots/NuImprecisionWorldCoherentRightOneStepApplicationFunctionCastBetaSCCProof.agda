module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaSCCProof
  where

-- File Charter:
--   * Closes target function-cast beta scheduling by structural recursion on
--     the caught source function's cast-spine rank.
--   * Uses the source lambda terminal at rank zero and the complete
--     source-function-cast matrix at each successor.
--   * Exposes unranked value, source-function-value, and arbitrary-function
--     schedulers without leaking the private rank.
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
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaDef
  using
  ( WorldCoherentRightOneStepApplicationFunctionCastBetaᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaValuesᵀ
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaFunctionCastValuesProof
  using
  (world-coherent-right-one-step-application-function-cast-beta-function-cast-values-at-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedDef
  using
  (WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaProof
  using
  (world-coherent-right-one-step-application-function-cast-beta-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaRankedDef
  using
  ( WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueAtᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaValuesAtᵀ
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueProof
  using
  (world-coherent-right-one-step-application-function-cast-beta-source-function-value-at-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaValuesProof
  using
  ( world-coherent-right-one-step-application-function-cast-beta-values-at-suc-proofᵀ
  ; world-coherent-right-one-step-application-function-cast-beta-values-at-zero-proofᵀ
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


private
  values-at :
    WorldCoherentLeftValueCatchupᵀ →
    WorldCoherentRightOneStepSourceCastFrames →
    WorldCoherentRightOneStepSourceConversionFrames →
    WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues →
    WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ →
    ∀ n →
    WorldCoherentRightOneStepApplicationFunctionCastBetaValuesAtᵀ n
  values-at catchup cast-frames conversion-frames paired lambda-terminal zero =
    world-coherent-right-one-step-application-function-cast-beta-values-at-zero-proofᵀ
      lambda-terminal
  values-at
      catchup cast-frames conversion-frames paired lambda-terminal (suc n) =
    world-coherent-right-one-step-application-function-cast-beta-values-at-suc-proofᵀ
      function-cast-at
    where
    lower-values =
      values-at catchup cast-frames conversion-frames paired lambda-terminal n

    lower-scheduler :
      WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueAtᵀ
        n
    lower-scheduler =
      world-coherent-right-one-step-application-function-cast-beta-source-function-value-at-proofᵀ
        catchup lower-values

    function-cast-at =
      world-coherent-right-one-step-application-function-cast-beta-function-cast-values-at-proofᵀ
        cast-frames conversion-frames paired lower-scheduler

  source-function-value-at :
    WorldCoherentLeftValueCatchupᵀ →
    WorldCoherentRightOneStepSourceCastFrames →
    WorldCoherentRightOneStepSourceConversionFrames →
    WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues →
    WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ →
    ∀ n →
    WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueAtᵀ
      n
  source-function-value-at
      catchup cast-frames conversion-frames paired lambda-terminal n =
    world-coherent-right-one-step-application-function-cast-beta-source-function-value-at-proofᵀ
      catchup
      (values-at
        catchup cast-frames conversion-frames paired lambda-terminal n)


world-coherent-right-one-step-application-function-cast-beta-values-scc-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepSourceCastFrames →
  WorldCoherentRightOneStepSourceConversionFrames →
  WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues →
  WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ →
  WorldCoherentRightOneStepApplicationFunctionCastBetaValuesᵀ
world-coherent-right-one-step-application-function-cast-beta-values-scc-proofᵀ
    catchup cast-frames conversion-frames paired lambda-terminal
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ vW′ =
  values-at catchup cast-frames conversion-frames paired lambda-terminal
    (targetFunctionCastSpineRank vL)
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vM vV′ vW′ refl


world-coherent-right-one-step-application-function-cast-beta-source-function-value-scc-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepSourceCastFrames →
  WorldCoherentRightOneStepSourceConversionFrames →
  WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues →
  WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ →
  WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueᵀ
world-coherent-right-one-step-application-function-cast-beta-source-function-value-scc-proofᵀ
    catchup cast-frames conversion-frames paired lambda-terminal
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ vW′ =
  source-function-value-at
    catchup cast-frames conversion-frames paired lambda-terminal
    (targetFunctionCastSpineRank vL)
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ vW′ refl


world-coherent-right-one-step-application-function-cast-beta-scc-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepSourceCastFrames →
  WorldCoherentRightOneStepSourceConversionFrames →
  WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues →
  WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ →
  WorldCoherentRightOneStepApplicationFunctionCastBetaᵀ
world-coherent-right-one-step-application-function-cast-beta-scc-proofᵀ
    catchup cast-frames conversion-frames paired lambda-terminal =
  world-coherent-right-one-step-application-function-cast-beta-proofᵀ
    catchup
    (source-function-value-at
      catchup cast-frames conversion-frames paired lambda-terminal)
