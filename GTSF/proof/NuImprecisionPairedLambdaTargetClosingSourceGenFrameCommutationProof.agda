module
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFrameCommutationProof
  where

-- File Charter:
--   * Proves the source-generic-frame commutation theorem from its exact
--     paired-reveal and paired-conceal constructor branches.
--   * Performs only the exhaustive paired-conversion dispatch; both branches
--     retain the fused final reveal and source allocation.
--   * Contains no semantic branch implementation, postulate, hole,
--     permissive option, or broad simulation import.

open import QuotientedTermImprecision using
  ( paired-conceal
  ; paired-reveal
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFrameCommutationDef
  using (PairedLambdaTargetClosingSourceGenFrameCommutationᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFramePairedConversionCasesDef
  using
  ( PairedLambdaTargetClosingSourceGenFramePairedConcealClosingᵀ
  ; PairedLambdaTargetClosingSourceGenFramePairedRevealClosingᵀ
  )


paired-lambda-target-closing-source-gen-frame-commutation-proofᵀ :
  PairedLambdaTargetClosingSourceGenFramePairedRevealClosingᵀ →
  PairedLambdaTargetClosingSourceGenFramePairedConcealClosingᵀ →
  PairedLambdaTargetClosingSourceGenFrameCommutationᵀ
paired-lambda-target-closing-source-gen-frame-commutation-proofᵀ
    reveal-closing conceal-closing
    vV noV vN′ noN′ relation framed inner
    prefix h⇑A final-reveal liftν lift∀
    (paired-reveal corr source-reveal target-reveal) =
  reveal-closing vV noV vN′ noN′ relation framed inner
    prefix h⇑A final-reveal liftν lift∀ corr
    source-reveal target-reveal
paired-lambda-target-closing-source-gen-frame-commutation-proofᵀ
    reveal-closing conceal-closing
    vV noV vN′ noN′ relation framed inner
    prefix h⇑A final-reveal liftν lift∀
    (paired-conceal corr source-conceal target-conceal) =
  conceal-closing vV noV vN′ noN′ relation framed inner
    prefix h⇑A final-reveal liftν lift∀ corr
    source-conceal target-conceal
