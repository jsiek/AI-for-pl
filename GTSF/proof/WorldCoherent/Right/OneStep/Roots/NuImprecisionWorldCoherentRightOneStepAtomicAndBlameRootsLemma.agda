module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepAtomicAndBlameRootsLemma
  where

-- File Charter:
--   * Exposes the canonical completed atomic-identity and target-blame roots.
--   * Contains no implementation, recursion, postulate, hole, or permissive
--     option.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepAtomicAndBlameRootsDef
  using (WorldCoherentRightOneStepAtomicAndBlameRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepAtomicAndBlameRootsProof
  using (world-coherent-right-one-step-atomic-and-blame-roots-proofᵀ)


world-coherent-right-one-step-atomic-and-blame-rootsᵀ :
  WorldCoherentRightOneStepAtomicAndBlameRoots
world-coherent-right-one-step-atomic-and-blame-rootsᵀ =
  world-coherent-right-one-step-atomic-and-blame-roots-proofᵀ
