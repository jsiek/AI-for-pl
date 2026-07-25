module
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetBulletLemma
  where

-- File Charter:
--   * Exposes canonical source-universal target-bullet closing.
--   * Supplies the completed structural source-value/target-bullet exclusion.
--   * Contains no additional theorem shape, postulate, hole, or permissive
--     option.

open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetBulletDef
  using (WorldCoherentRightSourceAllTargetBulletᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetBulletProof
  using (world-coherent-right-source-all-target-bullet-proofᵀ)
open import
  proof.Target.Core.NuImprecisionTargetBulletSourceValueExclusionLemma
  using (quotiented-target-bullet-excludes-source-valueᵀ)


world-coherent-right-source-all-target-bulletᵀ :
  WorldCoherentRightSourceAllTargetBulletᵀ
world-coherent-right-source-all-target-bulletᵀ =
  world-coherent-right-source-all-target-bullet-proofᵀ
    quotiented-target-bullet-excludes-source-valueᵀ
