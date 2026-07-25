module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationBlameRootsLemma
  where

-- File Charter:
--   * Exposes the strict target application-blame root assembly boundary.
--   * Leaves world-coherent source-to-target-value catch-up as an explicit
--     dependency of the right-argument blame root.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationBlameRootsDef
  using (WorldCoherentRightOneStepApplicationBlameRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationBlameRootsProof
  using
  (world-coherent-right-one-step-application-blame-roots-proofᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-application-blame-rootsᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationBlameRoots
world-coherent-right-one-step-application-blame-rootsᵀ =
  world-coherent-right-one-step-application-blame-roots-proofᵀ
