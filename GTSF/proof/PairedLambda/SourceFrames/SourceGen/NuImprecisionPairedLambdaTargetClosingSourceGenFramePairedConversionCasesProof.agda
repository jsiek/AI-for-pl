module
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFramePairedConversionCasesProof
  where

-- File Charter:
--   * Proves the frozen source-generic-frame paired-reveal and paired-conceal
--     closing branches by inverting their outer universal conversions.
--   * Delegates only the resulting fused generic-beta/inner-conversion
--     squares.
--   * Contains no postulate, hole, permissive option, broad simulation
--     import, recursive frame closer, or false source-only rotation.

open import Conversion using (conceal-all; reveal-all)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFramePairedConversionCasesDef
  using
  ( PairedLambdaTargetClosingSourceGenFramePairedConcealClosingᵀ
  ; PairedLambdaTargetClosingSourceGenFramePairedRevealClosingᵀ
  )
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingDef
  using (PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingDef
  using (PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ)


paired-lambda-target-closing-source-gen-frame-paired-reveal-closing-proofᵀ :
  PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ →
  PairedLambdaTargetClosingSourceGenFramePairedRevealClosingᵀ
paired-lambda-target-closing-source-gen-frame-paired-reveal-closing-proofᵀ
    closing vV noV vN′ noN′ relation framed inner
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀ corresponds
    (reveal-all source-reveal) (reveal-all target-reveal) =
  closing vV noV vN′ noN′ relation framed inner
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀ corresponds
    source-reveal target-reveal


paired-lambda-target-closing-source-gen-frame-paired-conceal-closing-proofᵀ :
  PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ →
  PairedLambdaTargetClosingSourceGenFramePairedConcealClosingᵀ
paired-lambda-target-closing-source-gen-frame-paired-conceal-closing-proofᵀ
    closing vV noV vN′ noN′ relation framed inner
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀ corresponds
    (conceal-all source-conceal) (conceal-all target-conceal) =
  closing vV noV vN′ noN′ relation framed inner
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀ corresponds
    source-conceal target-conceal
