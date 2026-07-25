module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepNuBlameRootLemma
  where

-- File Charter:
--   * Exposes the canonical target `blame-ν` root.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepNuBlameRootDef
  using (WorldCoherentRightOneStepNuBlameRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepNuBlameRootProof
  using (world-coherent-right-one-step-ν-blame-root-proofᵀ)


world-coherent-right-one-step-ν-blame-rootᵀ :
  WorldCoherentRightOneStepNuBlameRootᵀ
world-coherent-right-one-step-ν-blame-rootᵀ =
  world-coherent-right-one-step-ν-blame-root-proofᵀ
