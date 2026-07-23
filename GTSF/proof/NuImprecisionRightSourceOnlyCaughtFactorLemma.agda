module
  proof.NuImprecisionRightSourceOnlyCaughtFactorLemma
  where

-- File Charter:
--   * Exposes canonical factorization of completed right-value catch-up
--     beneath a source-only store lift.
--   * Keeps callers independent of lineage and world-invariant inversion.
--   * Contains no recursive dispatcher, result/view/outcome hierarchy,
--     postulate, hole, permissive option, termination bypass, or broad
--     simulation import.

open import
  proof.NuImprecisionRightSourceOnlyCaughtFactorDef
  using (RightSourceOnlyCaughtFactorᵀ)
open import
  proof.NuImprecisionRightSourceOnlyCaughtFactorProof
  using (right-source-only-caught-factor-proofᵀ)


right-source-only-caught-factorᵀ :
  RightSourceOnlyCaughtFactorᵀ
right-source-only-caught-factorᵀ
    liftρ caught context-eq empty-eq left-eq right-prefix =
  right-source-only-caught-factor-proofᵀ
    liftρ caught context-eq empty-eq left-eq right-prefix
