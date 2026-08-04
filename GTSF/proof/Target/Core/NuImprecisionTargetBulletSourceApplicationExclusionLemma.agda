module proof.Target.Core.NuImprecisionTargetBulletSourceApplicationExclusionLemma where

-- File Charter:
--   * Exposes the canonical source-application/target-bullet exclusion.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.Target.Core.NuImprecisionTargetBulletSourceApplicationExclusionDef
  using (QuotientedTargetBulletExcludesSourceApplicationᵀ)
open import
  proof.Target.Core.NuImprecisionTargetBulletSourceApplicationExclusionProof
  using (quotiented-target-bullet-excludes-source-application-proofᵀ)


quotiented-target-bullet-excludes-source-applicationᵀ :
  QuotientedTargetBulletExcludesSourceApplicationᵀ
quotiented-target-bullet-excludes-source-applicationᵀ =
  quotiented-target-bullet-excludes-source-application-proofᵀ
