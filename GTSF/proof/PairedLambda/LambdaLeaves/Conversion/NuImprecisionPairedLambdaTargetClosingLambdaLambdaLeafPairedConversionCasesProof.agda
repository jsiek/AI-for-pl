module
  proof.PairedLambda.LambdaLeaves.Conversion.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafPairedConversionCasesProof
  where

-- File Charter:
--   * Proves the frozen matched-`Λ`/`Λ` paired reveal and conceal closing
--     branches by exhaustively inverting their universal conversions.
--   * Delegates only the resulting fused inner structural conversions.
--   * Contains no postulate, hole, permissive option, broad simulation
--     import, pre-reveal rotation, or recursive frame closer.

open import Conversion using (conceal-all; reveal-all)
open import
  proof.PairedLambda.LambdaLeaves.Conversion.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafPairedConversionCasesDef
  using
  ( PairedLambdaTargetClosingLambdaLambdaLeafPairedConcealClosingᵀ
  ; PairedLambdaTargetClosingLambdaLambdaLeafPairedRevealClosingᵀ
  )
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingDef
  using
    (PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingDef
  using
    (PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ)


paired-lambda-target-closing-lambda-lambda-leaf-paired-reveal-closing-proofᵀ :
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafPairedRevealClosingᵀ
paired-lambda-target-closing-lambda-lambda-leaf-paired-reveal-closing-proofᵀ
    closing liftΛ liftγ vV noV vV′ noV′ V⊑V′
    {q = q}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀
    corresponds
    (reveal-all source-reveal) (reveal-all target-reveal) =
  closing liftΛ liftγ vV noV vV′ noV′ V⊑V′
    {q = q}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀
    corresponds
    source-reveal target-reveal


paired-lambda-target-closing-lambda-lambda-leaf-paired-conceal-closing-proofᵀ :
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafPairedConcealClosingᵀ
paired-lambda-target-closing-lambda-lambda-leaf-paired-conceal-closing-proofᵀ
    closing liftΛ liftγ vV noV vV′ noV′ V⊑V′
    {q = q}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀
    corresponds
    (conceal-all (conceal-all source-conceal))
    (conceal-all target-conceal) =
  closing liftΛ liftγ vV noV vV′ noV′ V⊑V′
    {q = q}
    prefix coherent exclusive wfL h⇑Aν final-reveal liftν lift∀
    corresponds
    source-conceal target-conceal
