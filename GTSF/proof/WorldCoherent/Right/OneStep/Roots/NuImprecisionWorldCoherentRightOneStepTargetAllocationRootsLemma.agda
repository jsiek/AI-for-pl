module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsLemma
  where

-- File Charter:
--   * Exposes the matched reveal-ν target-allocation root parameterized by
--     world-coherent left-value catch-up.
--   * Supplies the canonical focused matched-allocation lemma at the
--     target-root assembly boundary.
--   * Contains no recursion, postulate, hole, permissive option, dispatcher,
--     or `blame-ν` root.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsDef
  using (WorldCoherentRightOneStepTargetAllocationRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetAllocationRootsProof
  using (world-coherent-right-one-step-target-allocation-roots-proofᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Allocation.NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupLemma
  using (world-coherent-matched-nu-allocation-after-value-catchupᵀ)


world-coherent-right-one-step-target-allocation-rootsᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepTargetAllocationRoots
world-coherent-right-one-step-target-allocation-rootsᵀ =
  world-coherent-right-one-step-target-allocation-roots-proofᵀ
    world-coherent-matched-nu-allocation-after-value-catchupᵀ
