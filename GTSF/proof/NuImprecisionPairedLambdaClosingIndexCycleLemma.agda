module proof.NuImprecisionPairedLambdaClosingIndexCycleLemma where

-- File Charter:
--   * Assembles the canonical paired-lambda closing index-cycle theorem.
--   * Instantiates the higher-order exact-cycle proof with the strict common
--     target-extension obstruction.
--   * Contains no postulate, hole, permissive option, or broad simulation
--     import.

open import proof.NuImprecisionCommonTargetExtensionCycleProof using
  (common-target-extension-cycle-proofᵀ)
open import proof.NuImprecisionPairedLambdaClosingIndexCycleDef using
  (PairedLambdaClosingIndexCycleᵀ)
open import proof.NuImprecisionPairedLambdaClosingIndexCycleProof using
  (paired-lambda-closing-index-cycle-proofᵀ)


paired-lambda-closing-index-cycleᵀ :
  PairedLambdaClosingIndexCycleᵀ
paired-lambda-closing-index-cycleᵀ =
  paired-lambda-closing-index-cycle-proofᵀ
    common-target-extension-cycle-proofᵀ
