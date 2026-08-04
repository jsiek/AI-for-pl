module proof.Target.Core.NuImprecisionTargetValueSourceApplicationExclusionLemma where

-- File Charter:
--   * Exposes the canonical source-application/target-value exclusion.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import proof.Target.Core.NuImprecisionTargetValueSourceApplicationExclusionDef using
  (QuotientedTargetValueExcludesSourceApplicationᵀ)
open import proof.Target.Core.NuImprecisionTargetValueSourceApplicationExclusionProof using
  (quotiented-target-value-excludes-source-application-proofᵀ)


quotiented-target-value-excludes-source-applicationᵀ :
  QuotientedTargetValueExcludesSourceApplicationᵀ
quotiented-target-value-excludes-source-applicationᵀ =
  quotiented-target-value-excludes-source-application-proofᵀ
