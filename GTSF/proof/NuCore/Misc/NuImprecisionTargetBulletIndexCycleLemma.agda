module proof.NuCore.Misc.NuImprecisionTargetBulletIndexCycleLemma where

-- File Charter:
--   * Exposes the canonical target-bullet type-index cycle theorem.
--   * Supplies the completed common target-extension obstruction.
--   * Contains no additional theorem shape, store, term relation,
--     simulation, postulate, hole, or permissive option.

open import proof.NuCore.Misc.NuImprecisionCommonTargetExtensionCycleProof
  using (common-target-extension-cycle-proofᵀ)
open import proof.NuCore.Misc.NuImprecisionTargetBulletIndexCycleDef
  using (TargetBulletIndexCycleᵀ)
open import proof.NuCore.Misc.NuImprecisionTargetBulletIndexCycleProof
  using (target-bullet-index-cycle-proofᵀ)


target-bullet-index-cycleᵀ :
  TargetBulletIndexCycleᵀ
target-bullet-index-cycleᵀ =
  target-bullet-index-cycle-proofᵀ
    common-target-extension-cycle-proofᵀ
