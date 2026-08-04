module
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationFromViewProof
  where

-- File Charter:
--   * Derives continuation closing directly from frame-view projections and
--     the common continuation-value terminal theorem.
--   * Projects the reflexive pending continuation to the existing fused
--     frame-closing consumer type.
--   * Contains no semantic case analysis, postulate, hole, permissive option,
--     thirteen-handler dependency, continuation interpreter, or canonical
--     assembly.

open import
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationFromViewDef
  using (PairedLambdaTargetClosingContinuationFromViewᵀ)
open import
  proof.PairedLambda.Continuation.ValueTerminal.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalDef
  using (PairedLambdaTargetClosingContinuationValueTerminalᵀ)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewProperties
  using
  ( paired-lambda-target-closing-frame-view-relation
  ; paired-lambda-target-closing-frame-view-source-no-bullet
  ; paired-lambda-target-closing-frame-view-source-value
  ; paired-lambda-target-closing-frame-view-target-no-bullet
  ; paired-lambda-target-closing-frame-view-target-value
  )
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (pending-refl)
open import
  proof.Source.NuPaired.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingDef
  using
  (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ)


paired-lambda-target-closing-continuation-from-view-proofᵀ :
  PairedLambdaTargetClosingContinuationValueTerminalᵀ →
  PairedLambdaTargetClosingContinuationFromViewᵀ
paired-lambda-target-closing-continuation-from-view-proofᵀ terminal view =
  terminal
    (paired-lambda-target-closing-frame-view-source-value view)
    (paired-lambda-target-closing-frame-view-source-no-bullet view)
    (paired-lambda-target-closing-frame-view-target-value view)
    (paired-lambda-target-closing-frame-view-target-no-bullet view)
    (paired-lambda-target-closing-frame-view-relation view)


paired-lambda-target-closing-continuation-from-view-frame-closing-proofᵀ :
  PairedLambdaTargetClosingContinuationFromViewᵀ →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ
paired-lambda-target-closing-continuation-from-view-frame-closing-proofᵀ
    close prefix coherent exclusive wfL h⇑A reveal liftν lift∀
    view conversion =
  close view pending-refl prefix coherent exclusive wfL
    h⇑A reveal liftν lift∀ conversion
