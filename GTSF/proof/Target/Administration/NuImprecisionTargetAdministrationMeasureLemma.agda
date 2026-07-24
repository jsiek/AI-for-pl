module
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureLemma
  where

-- File Charter:
--   * Exposes canonical strict removal of one pending target-cast head.
--   * Exposes canonical strict rank growth under inert value absorption.
--   * Exposes the canonical paired-`Λ` allocation continuation decrease.
--   * Exposes rank invariance for right-allocation-shifted pending tails.
--   * Keeps ranked target-administration workers independent of arithmetic
--     proof implementation.
--   * Contains no additional theorem shape, semantic recursion, postulate,
--     hole, permissive option, or termination bypass.

open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureDef
  using
  ( TargetInertValueAdministrationIncreaseᵀ
  ; TargetPairedLambdaAllocationContinuationRankDecreaseᵀ
  ; TargetPairedLambdaRightAllocationContinuationRankDecreaseᵀ
  ; TargetPendingAdministrationTailDecreaseᵀ
  ; TargetPendingAdministrationShiftMapRankInvariantᵀ
  )
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureProof
  using
  ( target-inert-value-administration-increase-proofᵀ
  ; target-paired-lambda-allocation-continuation-rank-decrease-proofᵀ
  ; target-paired-lambda-right-allocation-continuation-rank-decrease-proofᵀ
  ; target-pending-administration-tail-decrease-proofᵀ
  ; target-pending-administration-shift-map-rank-invariant-proofᵀ
  )


target-pending-administration-tail-decreaseᵀ :
  TargetPendingAdministrationTailDecreaseᵀ
target-pending-administration-tail-decreaseᵀ =
  target-pending-administration-tail-decrease-proofᵀ


target-inert-value-administration-increaseᵀ :
  TargetInertValueAdministrationIncreaseᵀ
target-inert-value-administration-increaseᵀ =
  target-inert-value-administration-increase-proofᵀ


target-paired-lambda-allocation-continuation-rank-decreaseᵀ :
  TargetPairedLambdaAllocationContinuationRankDecreaseᵀ
target-paired-lambda-allocation-continuation-rank-decreaseᵀ =
  target-paired-lambda-allocation-continuation-rank-decrease-proofᵀ


target-pending-administration-shift-map-rank-invariantᵀ :
  TargetPendingAdministrationShiftMapRankInvariantᵀ
target-pending-administration-shift-map-rank-invariantᵀ =
  target-pending-administration-shift-map-rank-invariant-proofᵀ


target-paired-lambda-right-allocation-continuation-rank-decreaseᵀ :
  TargetPairedLambdaRightAllocationContinuationRankDecreaseᵀ
target-paired-lambda-right-allocation-continuation-rank-decreaseᵀ =
  target-paired-lambda-right-allocation-continuation-rank-decrease-proofᵀ
