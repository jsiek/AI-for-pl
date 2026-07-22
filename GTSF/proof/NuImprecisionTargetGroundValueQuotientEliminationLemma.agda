module proof.NuImprecisionTargetGroundValueQuotientEliminationLemma where

-- File Charter:
--   * Assembles target-ground value quotient elimination from its proof.
--   * Exposes the canonical inhabitant of the separately stated theorem.
--   * Keeps downstream proof modules free to depend on proof internals.

open import
  proof.NuImprecisionTargetGroundValueQuotientEliminationDef using
  (TargetGroundValueQuotientEliminationᵀ)
open import
  proof.NuImprecisionTargetGroundValueQuotientEliminationProof using
  (target-ground-value-quotient-elimination-proofᵀ)


target-ground-value-quotient-eliminationᵀ :
  TargetGroundValueQuotientEliminationᵀ
target-ground-value-quotient-eliminationᵀ =
  target-ground-value-quotient-elimination-proofᵀ
