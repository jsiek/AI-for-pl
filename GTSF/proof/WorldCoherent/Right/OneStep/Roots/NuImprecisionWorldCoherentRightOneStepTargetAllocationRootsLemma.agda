module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsLemma
  where

-- File Charter:
--   * Exposes the canonical four target-allocation roots parameterized by
--     world-coherent left-value catch-up.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, dispatcher, or `blame-ν` root.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsDef
  using (WorldCoherentRightOneStepTargetAllocationRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsProof
  using (world-coherent-right-one-step-target-allocation-roots-proofᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-target-allocation-rootsᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepTargetAllocationRoots
world-coherent-right-one-step-target-allocation-rootsᵀ =
  world-coherent-right-one-step-target-allocation-roots-proofᵀ
