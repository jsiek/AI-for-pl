module
  proof.Target.Administration.NuImprecisionTargetPendingLambdaAllocationTraceLemma
  where

-- File Charter:
--   * Exposes the canonical exact target allocation trace beneath arbitrary
--     pending target casts.
--   * Supplies the completed structural proof without a compatibility layer,
--     postulate, hole, or permissive option.

open import
  proof.Target.Administration.NuImprecisionTargetPendingLambdaAllocationTraceDef
  using (TargetPendingLambdaAllocationTraceᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetPendingLambdaAllocationTraceProof
  using (target-pending-lambda-allocation-trace-proofᵀ)


target-pending-lambda-allocation-traceᵀ :
  TargetPendingLambdaAllocationTraceᵀ
target-pending-lambda-allocation-traceᵀ
    {W′ = W′} {s = s} {cs = cs} =
  target-pending-lambda-allocation-trace-proofᵀ
    {W′ = W′} {s = s} {cs = cs}
