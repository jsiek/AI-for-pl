module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveDeltaRootLemma
  where

-- File Charter:
--   * Exposes the strict target natural-addition delta root.
--   * Leaves world-coherent source-to-target-value catch-up as its explicit
--     semantic dependency.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, blame root, or compatibility wrapper.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveDeltaRootDef
  using (WorldCoherentRightOneStepPrimitiveDeltaRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveDeltaRootProof
  using
  (world-coherent-right-one-step-primitive-delta-root-proofᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-primitive-delta-rootᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepPrimitiveDeltaRootᵀ
world-coherent-right-one-step-primitive-delta-rootᵀ =
  world-coherent-right-one-step-primitive-delta-root-proofᵀ
