module
  proof.Target.Core.NuImprecisionTargetBulletSourceValueExclusionLemma
  where

-- File Charter:
--   * Exposes the canonical source-value/target-bullet exclusion.
--   * Supplies the completed target-bullet type-index cycle theorem.
--   * Contains no additional theorem shape, postulate, hole, or permissive
--     option.

open import
  proof.NuCore.Misc.NuImprecisionTargetBulletIndexCycleLemma
  using (target-bullet-index-cycleᵀ)
open import
  proof.Target.Core.NuImprecisionTargetBulletSourceValueExclusionDef
  using (QuotientedTargetBulletExcludesSourceValueᵀ)
open import
  proof.Target.Core.NuImprecisionTargetBulletSourceValueExclusionProof
  using (quotiented-target-bullet-excludes-source-value-proofᵀ)


quotiented-target-bullet-excludes-source-valueᵀ :
  QuotientedTargetBulletExcludesSourceValueᵀ
quotiented-target-bullet-excludes-source-valueᵀ =
  quotiented-target-bullet-excludes-source-value-proofᵀ
    target-bullet-index-cycleᵀ
