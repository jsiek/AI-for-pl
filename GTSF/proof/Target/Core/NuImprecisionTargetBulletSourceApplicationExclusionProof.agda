module proof.Target.Core.NuImprecisionTargetBulletSourceApplicationExclusionProof where

-- File Charter:
--   * Proves directly that a source application cannot be related to a
--     target runtime bullet by the syntax-directed term relation.
--   * Contains no catch-all, postulate, hole, or permissive option.

open import
  proof.Target.Core.NuImprecisionTargetBulletSourceApplicationExclusionDef
  using (QuotientedTargetBulletExcludesSourceApplicationᵀ)
open import
  proof.Target.Core.NuImprecisionTargetValueSourceApplicationExclusionLemma
  using (quotiented-target-value-excludes-source-applicationᵀ)


quotiented-target-bullet-excludes-source-application-proofᵀ :
  QuotientedTargetBulletExcludesSourceApplicationᵀ
quotiented-target-bullet-excludes-source-application-proofᵀ
    ()
