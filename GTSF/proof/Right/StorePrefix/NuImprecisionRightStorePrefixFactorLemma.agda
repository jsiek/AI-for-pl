module proof.Right.StorePrefix.NuImprecisionRightStorePrefixFactorLemma where

-- File Charter:
--   * Supplies the canonical right-store prefix factor from its strict proof.
--   * Keeps callers independent of the worker proof module.
--   * Contains no postulate, hole, permissive option, or simulation import.

open import proof.Right.StorePrefix.NuImprecisionRightStorePrefixFactorDef using
  (RightStorePrefixFactorᵀ)
open import proof.Right.StorePrefix.NuImprecisionRightStorePrefixFactorProof using
  (right-store-prefix-factor-proofᵀ)


right-store-prefix-factorᵀ : RightStorePrefixFactorᵀ
right-store-prefix-factorᵀ = right-store-prefix-factor-proofᵀ
