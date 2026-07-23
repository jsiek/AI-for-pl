module
  proof.NuImprecisionRightOnlyStorePrefixLeftLiftFactorLemma
  where

-- File Charter:
--   * Exposes canonical target-only prefix factorization across a source-only
--     relational-store lift.
--   * Keeps callers independent of the structural worker proof.
--   * Contains no term relation, postulate, hole, permissive option,
--     termination bypass, or broad simulation import.

open import
  proof.NuImprecisionRightOnlyStorePrefixLeftLiftFactorDef
  using (RightOnlyStorePrefixLeftLiftFactorᵀ)
open import
  proof.NuImprecisionRightOnlyStorePrefixLeftLiftFactorProof
  using (right-only-store-prefix-left-lift-factor-proofᵀ)


right-only-store-prefix-left-lift-factorᵀ :
  RightOnlyStorePrefixLeftLiftFactorᵀ
right-only-store-prefix-left-lift-factorᵀ liftρ prefix =
  right-only-store-prefix-left-lift-factor-proofᵀ
    liftρ prefix
