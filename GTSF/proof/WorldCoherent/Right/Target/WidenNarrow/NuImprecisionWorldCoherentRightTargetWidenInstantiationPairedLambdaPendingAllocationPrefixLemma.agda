module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixLemma
  where

-- File Charter:
--   * Exposes the canonical source-silent paired-lambda target-allocation
--     prefix beneath an arbitrary hereditary pending-cast spine and for an
--     arbitrary universal root.
--   * Supplies the canonical post-beta relation, source-bullet transport,
--     right-allocation spine transport, and exact pending allocation trace to
--     the strict higher-order proof.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.Right.AllocationRuntime.NuImprecisionRightTargetAllocationSourceBulletTransportProof
  using (right-target-allocation-source-bullet-transport-proofᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationSpineRightAllocationLemma
  using (target-administration-spine-right-allocationᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetPendingLambdaAllocationTraceLemma
  using (target-pending-lambda-allocation-traceᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixProof
  using
  (world-coherent-right-target-widen-instantiation-paired-lambda-pending-allocation-prefix-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextProof
  using
  (world-coherent-right-target-widen-instantiation-paired-lambda-post-beta-context-proofᵀ)


world-coherent-right-target-widen-instantiation-paired-lambda-pending-allocation-prefixᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedLambdaPendingAllocationPrefixᵀ
world-coherent-right-target-widen-instantiation-paired-lambda-pending-allocation-prefixᵀ =
  world-coherent-right-target-widen-instantiation-paired-lambda-pending-allocation-prefix-proofᵀ
    world-coherent-right-target-widen-instantiation-paired-lambda-post-beta-context-proofᵀ
    right-target-allocation-source-bullet-transport-proofᵀ
    target-administration-spine-right-allocationᵀ
    (λ {W′} {s} {cs} vW′ noW′ →
      target-pending-lambda-allocation-traceᵀ
        {W′ = W′} {s = s} {cs = cs} vW′ noW′)
