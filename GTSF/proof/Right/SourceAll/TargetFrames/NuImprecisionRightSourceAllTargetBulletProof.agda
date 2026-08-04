module
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetBulletProof
  where

-- File Charter:
--   * Proves source-universal target-bullet closing by structural QTI
--     exclusion.
--   * Peeling source values ultimately exposes the impossible right-only
--     allocation indices; no recursive closing callback is required.
--   * Contains no dispatcher, postulate, hole, or permissive option.

open import Data.Empty using (⊥-elim)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetBulletDef
  using (WorldCoherentRightSourceAllTargetBulletᵀ)
open import
  proof.Target.Core.NuImprecisionTargetBulletSourceValueExclusionDef
  using (QuotientedTargetBulletExcludesSourceValueᵀ)


world-coherent-right-source-all-target-bullet-proofᵀ :
  QuotientedTargetBulletExcludesSourceValueᵀ →
  WorldCoherentRightSourceAllTargetBulletᵀ
world-coherent-right-source-all-target-bullet-proofᵀ
    exclude prefix coherent exclusive unique wfR runtime
    vV noV liftρ liftγ relation =
  ⊥-elim (exclude vV relation)
