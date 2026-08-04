module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepNuBlameRootProof
  where

-- File Charter:
--   * Proves the paired outer-`ν` blame root by catching the source body up
--     to blame and lifting that trace through `ν` and `blame-ν`.
--   * Produces only a source-blame outcome, so no successor world or lineage
--     is required.
--   * Contains no recursion, postulate, hole, permissive option, catch-all,
--     or compatibility wrapper.

open import Data.Product using (_,_)
open import proof.Core.Properties.NuRuntimeProperties using (runtime-ν)
open import
  proof.Target.Core.NuImprecisionTargetBlameCatchup
  using
  ( left-catchup-target-blameᵀ
  ; ν-blame-tailᵀ
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (world-indexed-outcome-source-blame)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepNuBlameRootDef
  using (WorldCoherentRightOneStepNuBlameRootᵀ)


world-coherent-right-one-step-ν-blame-root-proofᵀ :
  WorldCoherentRightOneStepNuBlameRootᵀ
world-coherent-right-one-step-ν-blame-root-proofᵀ okν N⊑blame
    with left-catchup-target-blameᵀ (runtime-ν okν) N⊑blame
world-coherent-right-one-step-ν-blame-root-proofᵀ okν N⊑blame
    | χs , N↠blame =
  world-indexed-outcome-source-blame (ν-blame-tailᵀ N↠blame)
