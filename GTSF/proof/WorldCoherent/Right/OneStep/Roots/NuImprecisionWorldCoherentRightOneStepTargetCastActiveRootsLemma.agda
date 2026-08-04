module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetCastActiveRootsLemma
  where

-- File Charter:
--   * Exposes the strict active target-cast root assembly boundary.
--   * Makes the seven remaining semantic cells explicit to future backward
--     dispatcher consumers.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, compatibility wrapper, or unconditional semantic claim.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepAtomicAndBlameRootsDef
  using (WorldCoherentRightOneStepAtomicAndBlameRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetCastActiveRootsDef
  using
  ( WorldCoherentRightOneStepTargetCastActiveRoots
  ; WorldCoherentRightOneStepTargetCastSemanticRoots
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepTargetCastActiveRootsProof
  using
  (world-coherent-right-one-step-target-cast-active-roots-proofᵀ)


world-coherent-right-one-step-target-cast-active-rootsᵀ :
  WorldCoherentRightOneStepAtomicAndBlameRoots →
  WorldCoherentRightOneStepTargetCastSemanticRoots →
  WorldCoherentRightOneStepTargetCastActiveRoots
world-coherent-right-one-step-target-cast-active-rootsᵀ =
  world-coherent-right-one-step-target-cast-active-roots-proofᵀ
