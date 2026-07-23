module proof.NuImprecisionSingleSubstitutionEnvironmentLemma where

-- File Charter:
--   * Assembles the canonical single-substitution environment family.
--   * Supplies strict term-context insertion and both assumption-unique
--     type-binder lifting proofs to the frame-recursive implementation.
--   * Contains no relation traversal, postulate, hole, or permissive option.

open import proof.NuImprecisionSingleSubstitutionEnvironmentDef using
  (QuotientedSingleSubstitutionEnvironmentᵀ)
open import proof.NuImprecisionSingleSubstitutionEnvironmentProof using
  (quotiented-single-substitution-environment-proofᵀ)
open import
  proof.NuImprecisionSubstitutionEnvironmentTypeLiftProof using
  ( quotiented-substitution-environment-left-type-lift-proofᵀ
  ; quotiented-substitution-environment-paired-type-lift-proofᵀ
  )
open import proof.NuImprecisionTermContextShiftProof using
  (quotiented-term-context-shift-proofᵀ)


quotiented-single-substitution-environment-lemmaᵀ :
  QuotientedSingleSubstitutionEnvironmentᵀ
quotiented-single-substitution-environment-lemmaᵀ =
  quotiented-single-substitution-environment-proofᵀ
    quotiented-term-context-shift-proofᵀ
    quotiented-substitution-environment-paired-type-lift-proofᵀ
    quotiented-substitution-environment-left-type-lift-proofᵀ
