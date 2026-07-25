module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetConversionRootsLemma
  where

-- File Charter:
--   * Exposes the strict target-conversion root assembly boundary.
--   * Leaves the atomic leaves and world-coherent reveal-unseal catch-up as
--     explicit dependencies.
--   * Contains no implementation, recursion, postulate, hole, or permissive
--     option.

open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentTargetRevealRootDef
  using (WorldCoherentTargetRevealRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepAtomicAndBlameRootsDef
  using (WorldCoherentRightOneStepAtomicAndBlameRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetConversionRootsDef
  using (WorldCoherentRightOneStepTargetConversionRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetConversionRootsProof
  using
  (world-coherent-right-one-step-target-conversion-roots-proofᵀ)


world-coherent-right-one-step-target-conversion-rootsᵀ :
  WorldCoherentRightOneStepAtomicAndBlameRoots →
  WorldCoherentTargetRevealRootᵀ →
  WorldCoherentRightOneStepTargetConversionRoots
world-coherent-right-one-step-target-conversion-rootsᵀ =
  world-coherent-right-one-step-target-conversion-roots-proofᵀ
