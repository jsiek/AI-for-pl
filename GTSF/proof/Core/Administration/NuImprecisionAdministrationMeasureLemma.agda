module
  proof.Core.Administration.NuImprecisionAdministrationMeasureLemma
  where

-- File Charter:
--   * Exposes canonical strict removal of one pending cast head.
--   * Exposes canonical strict rank growth under inert value absorption.
--   * Exposes the canonical `Λ` allocation continuation decrease.
--   * Exposes rank invariance for allocation-shifted pending tails.
--   * Keeps ranked administration workers independent of arithmetic
--     proof implementation.
--   * Contains no additional theorem shape, semantic recursion, postulate,
--     hole, permissive option, or termination bypass.

open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureDef
  using
  ( InertValueAdministrationIncreaseᵀ
  ; LambdaAllocationContinuationRankDecreaseᵀ
  ; LambdaShiftedAllocationContinuationRankDecreaseᵀ
  ; PendingAdministrationTailDecreaseᵀ
  ; PendingAdministrationShiftMapRankInvariantᵀ
  )
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureProof
  using
  ( inert-value-administration-increase-proofᵀ
  ; lambda-allocation-continuation-rank-decrease-proofᵀ
  ; lambda-shifted-allocation-continuation-rank-decrease-proofᵀ
  ; pending-administration-tail-decrease-proofᵀ
  ; pending-administration-shift-map-rank-invariant-proofᵀ
  )


pending-administration-tail-decreaseᵀ :
  PendingAdministrationTailDecreaseᵀ
pending-administration-tail-decreaseᵀ =
  pending-administration-tail-decrease-proofᵀ


inert-value-administration-increaseᵀ :
  InertValueAdministrationIncreaseᵀ
inert-value-administration-increaseᵀ =
  inert-value-administration-increase-proofᵀ


lambda-allocation-continuation-rank-decreaseᵀ :
  LambdaAllocationContinuationRankDecreaseᵀ
lambda-allocation-continuation-rank-decreaseᵀ =
  lambda-allocation-continuation-rank-decrease-proofᵀ


pending-administration-shift-map-rank-invariantᵀ :
  PendingAdministrationShiftMapRankInvariantᵀ
pending-administration-shift-map-rank-invariantᵀ =
  pending-administration-shift-map-rank-invariant-proofᵀ


lambda-shifted-allocation-continuation-rank-decreaseᵀ :
  LambdaShiftedAllocationContinuationRankDecreaseᵀ
lambda-shifted-allocation-continuation-rank-decreaseᵀ =
  lambda-shifted-allocation-continuation-rank-decrease-proofᵀ
