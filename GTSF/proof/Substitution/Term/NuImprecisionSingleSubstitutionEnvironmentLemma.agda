module proof.Substitution.Term.NuImprecisionSingleSubstitutionEnvironmentLemma where

-- File Charter:
--   * Assembles the canonical single-substitution environment family.
--   * Supplies strict term-context insertion and both assumption-unique
--     type-binder lifting proofs to the frame-recursive implementation.
--   * Contains no relation traversal, postulate, hole, or permissive option.

open import proof.Substitution.Term.NuImprecisionSingleSubstitutionEnvironmentDef using
  (QuotientedSingleSubstitutionEnvironmentᵀ)
open import proof.Substitution.Term.NuImprecisionSingleSubstitutionEnvironmentProof using
  (quotiented-single-substitution-environment-proofᵀ)
open import
  proof.Substitution.Term.NuImprecisionSubstitutionEnvironmentTypeLiftProof using
  ( quotiented-substitution-environment-left-type-lift-proofᵀ
  ; quotiented-substitution-environment-paired-type-lift-proofᵀ
  )
open import proof.Substitution.Term.NuImprecisionTermContextShiftProof using
  (quotiented-term-context-shift-proofᵀ)


quotiented-single-substitution-environment-lemmaᵀ :
  QuotientedSingleSubstitutionEnvironmentᵀ
quotiented-single-substitution-environment-lemmaᵀ =
  quotiented-single-substitution-environment-proofᵀ
    quotiented-term-context-shift-proofᵀ
    quotiented-substitution-environment-paired-type-lift-proofᵀ
    quotiented-substitution-environment-left-type-lift-proofᵀ
