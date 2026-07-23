module
  proof.PairedLambda.LambdaLeaves.MatchedUnseal.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingLemma
  where

-- File Charter:
--   * Assembles the canonical matched/matched double-unseal closing leaf.
--   * Supplies the strict conversion-absence identity and paired-lambda
--     closing index-cycle theorems to the higher-order proof.
--   * Contains no postulate, hole, permissive option, recursive closer, or
--     broad simulation import.

open import proof.NuCore.Relations.NuImprecisionConversionAbsenceIdentityLemma using
  (reveal-absent-source-identityᵀ)
open import proof.PairedLambda.LambdaLeaves.NuLeaf.NuImprecisionPairedLambdaClosingIndexCycleLemma using
  (paired-lambda-closing-index-cycleᵀ)
open import
  proof.PairedLambda.LambdaLeaves.MatchedUnseal.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingDef
  using
    (PairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingᵀ)
open import
  proof.PairedLambda.LambdaLeaves.MatchedUnseal.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingProof
  using
    (paired-lambda-target-closing-lambda-lambda-leaf-matched-unseal-closing-proofᵀ)


paired-lambda-target-closing-lambda-lambda-leaf-matched-unseal-closingᵀ :
  PairedLambdaTargetClosingLambdaLambdaLeafMatchedUnsealClosingᵀ
paired-lambda-target-closing-lambda-lambda-leaf-matched-unseal-closingᵀ =
  paired-lambda-target-closing-lambda-lambda-leaf-matched-unseal-closing-proofᵀ
    reveal-absent-source-identityᵀ
    paired-lambda-closing-index-cycleᵀ
