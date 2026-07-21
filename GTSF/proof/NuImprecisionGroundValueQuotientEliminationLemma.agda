module proof.NuImprecisionGroundValueQuotientEliminationLemma where

-- File Charter:
--   * Assembles ground-value quotient elimination from its proof module.
--   * Exposes the canonical inhabitant of the separately stated theorem.
--   * Keeps downstream proof modules free to depend on the Def boundary.

open import
  proof.NuImprecisionGroundValueQuotientEliminationDef using
  (GroundValueQuotientEliminationᵀ)
open import
  proof.NuImprecisionGroundValueQuotientEliminationProof using
  (ground-value-quotient-elimination-proofᵀ)


ground-value-quotient-eliminationᵀ :
  GroundValueQuotientEliminationᵀ
ground-value-quotient-eliminationᵀ =
  ground-value-quotient-elimination-proofᵀ
