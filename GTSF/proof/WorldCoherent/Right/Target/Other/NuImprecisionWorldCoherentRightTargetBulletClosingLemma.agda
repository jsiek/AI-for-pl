module
  proof.WorldCoherent.Right.Target.Other.NuImprecisionWorldCoherentRightTargetBulletClosingLemma
  where

-- File Charter:
--   * Exposes canonical target runtime-bullet closing.
--   * Supplies the completed type-only target-bullet index-cycle theorem.
--   * Contains no target administration, recursive worker, result/view/
--     outcome type, postulate, hole, permissive option, compatibility
--     wrapper, or broad simulation import.

open import
  proof.NuCore.Misc.NuImprecisionTargetBulletIndexCycleLemma
  using (target-bullet-index-cycleᵀ)
open import
  proof.WorldCoherent.Right.Target.Other.NuImprecisionWorldCoherentRightTargetBulletClosingDef
  using (WorldCoherentRightTargetBulletClosingᵀ)
open import
  proof.WorldCoherent.Right.Target.Other.NuImprecisionWorldCoherentRightTargetBulletClosingProof
  using (world-coherent-right-target-bullet-closing-proofᵀ)


world-coherent-right-target-bullet-closingᵀ :
  WorldCoherentRightTargetBulletClosingᵀ
world-coherent-right-target-bullet-closingᵀ =
  world-coherent-right-target-bullet-closing-proofᵀ
    target-bullet-index-cycleᵀ
