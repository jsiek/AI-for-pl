module proof.NuImprecisionTargetBulletSourceApplicationExclusionProof where

-- File Charter:
--   * Exhaustively peels target-bullet allocation prefixes and invokes the
--     canonical application/target-value exclusion at the bullet root.
--   * Contains no catch-all, postulate, hole, or permissive option.

open import QuotientedTermImprecision using
  (allocation-prefixᵀ; ⊑αᵀ)
open import
  proof.NuImprecisionTargetBulletSourceApplicationExclusionDef
  using (QuotientedTargetBulletExcludesSourceApplicationᵀ)
open import
  proof.NuImprecisionTargetValueSourceApplicationExclusionLemma
  using (quotiented-target-value-excludes-source-applicationᵀ)


quotiented-target-bullet-excludes-source-application-proofᵀ :
  QuotientedTargetBulletExcludesSourceApplicationᵀ
quotiented-target-bullet-excludes-source-application-proofᵀ
    (allocation-prefixᵀ prefix inner source⊢ target⊢) =
  quotiented-target-bullet-excludes-source-application-proofᵀ inner
quotiented-target-bullet-excludes-source-application-proofᵀ
    (⊑αᵀ vV noV hA liftρ liftγ inner r M⊢ V•⊢) =
  quotiented-target-value-excludes-source-applicationᵀ inner vV
