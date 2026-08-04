module
  proof.Left.LiftedStore.NuImprecisionLeftLiftedStorePrefixFactorLemma
  where

-- File Charter:
--   * Exposes the canonical inverse source-only lifted-store prefix
--     factorization theorem.
--   * Keeps callers independent of the structural worker proof.
--   * Contains no term relation, postulate, hole, permissive option, or
--     compatibility wrapper.

open import
  proof.Left.LiftedStore.NuImprecisionLeftLiftedStorePrefixFactorDef
  using (LeftLiftedStorePrefixFactorᵀ)
open import
  proof.Left.LiftedStore.NuImprecisionLeftLiftedStorePrefixFactorProof
  using (left-lifted-store-prefix-factor-proofᵀ)


left-lifted-store-prefix-factorᵀ :
  LeftLiftedStorePrefixFactorᵀ
left-lifted-store-prefix-factorᵀ =
  left-lifted-store-prefix-factor-proofᵀ
