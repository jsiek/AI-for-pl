module proof.NuCore.Relations.NuImprecisionConversionAbsenceIdentityLemma where

-- File Charter:
--   * Exposes the canonical reveal-source and conceal-target absence identity
--     lemmas.
--   * Assembles only the checked mutual structural proof; contains no proof
--     recursion, postulate, hole, permissive option, or simulation import.

open import proof.NuCore.Relations.NuImprecisionConversionAbsenceIdentityDef using
  ( ConcealAbsentTargetIdentityᵀ
  ; RevealAbsentSourceIdentityᵀ
  )
open import proof.NuCore.Relations.NuImprecisionConversionAbsenceIdentityProof using
  ( conceal-absent-target-identity-proofᵀ
  ; reveal-absent-source-identity-proofᵀ
  )


reveal-absent-source-identityᵀ : RevealAbsentSourceIdentityᵀ
reveal-absent-source-identityᵀ =
  reveal-absent-source-identity-proofᵀ


conceal-absent-target-identityᵀ : ConcealAbsentTargetIdentityᵀ
conceal-absent-target-identityᵀ =
  conceal-absent-target-identity-proofᵀ
