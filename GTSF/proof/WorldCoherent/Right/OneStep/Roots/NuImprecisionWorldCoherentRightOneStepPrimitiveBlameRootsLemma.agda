module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveBlameRootsLemma
  where

-- File Charter:
--   * Exposes the strict target primitive-blame root assembly boundary.
--   * Leaves world-coherent source-to-target-value catch-up as an explicit
--     dependency of the right-operand blame root.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, delta root, or compatibility wrapper.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveBlameRootsDef
  using (WorldCoherentRightOneStepPrimitiveBlameRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveBlameRootsProof
  using
  (world-coherent-right-one-step-primitive-blame-roots-proofᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-primitive-blame-rootsᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepPrimitiveBlameRoots
world-coherent-right-one-step-primitive-blame-rootsᵀ =
  world-coherent-right-one-step-primitive-blame-roots-proofᵀ
