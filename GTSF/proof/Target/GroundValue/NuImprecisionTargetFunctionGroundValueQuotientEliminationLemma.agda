module proof.Target.GroundValue.NuImprecisionTargetFunctionGroundValueQuotientEliminationLemma where

-- File Charter:
--   * Assembles target-function-ground value quotient elimination.
--   * Exposes the canonical inhabitant of the separately stated theorem.
--   * Keeps downstream proof modules free to depend on proof internals.

open import
  proof.Target.GroundValue.NuImprecisionTargetFunctionGroundValueQuotientEliminationDef
  using (TargetFunctionGroundValueQuotientEliminationᵀ)
open import
  proof.Target.GroundValue.NuImprecisionTargetFunctionGroundValueQuotientEliminationProof
  using (target-function-ground-value-quotient-elimination-proofᵀ)


target-function-ground-value-quotient-eliminationᵀ :
  TargetFunctionGroundValueQuotientEliminationᵀ
target-function-ground-value-quotient-eliminationᵀ =
  target-function-ground-value-quotient-elimination-proofᵀ
