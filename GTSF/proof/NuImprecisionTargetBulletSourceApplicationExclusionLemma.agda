module proof.NuImprecisionTargetBulletSourceApplicationExclusionLemma where

-- File Charter:
--   * Exposes the canonical source-application/target-bullet exclusion.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.NuImprecisionTargetBulletSourceApplicationExclusionDef
  using (QuotientedTargetBulletExcludesSourceApplicationᵀ)
open import
  proof.NuImprecisionTargetBulletSourceApplicationExclusionProof
  using (quotiented-target-bullet-excludes-source-application-proofᵀ)


quotiented-target-bullet-excludes-source-applicationᵀ :
  QuotientedTargetBulletExcludesSourceApplicationᵀ
quotiented-target-bullet-excludes-source-applicationᵀ =
  quotiented-target-bullet-excludes-source-application-proofᵀ
