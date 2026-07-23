module proof.NuImprecisionStorePrefixLiftLemma where

-- File Charter:
--   * Exposes the canonical paired, source-only, and target-only store-prefix
--     lift theorems.
--   * Keeps callers independent of the structural worker proof.
--   * Contains no simulation, postulate, hole, permissive option, or wrapper
--     carrier.

open import proof.NuImprecisionStorePrefixLiftDef using
  (LeftStorePrefixLiftᵀ; PairedStorePrefixLiftᵀ; RightStorePrefixLiftᵀ)
open import proof.NuImprecisionStorePrefixLiftProof using
  ( left-store-prefix-lift-proofᵀ
  ; paired-store-prefix-lift-proofᵀ
  ; right-store-prefix-lift-proofᵀ
  )


paired-store-prefix-liftᵀ : PairedStorePrefixLiftᵀ
paired-store-prefix-liftᵀ = paired-store-prefix-lift-proofᵀ


left-store-prefix-liftᵀ : LeftStorePrefixLiftᵀ
left-store-prefix-liftᵀ = left-store-prefix-lift-proofᵀ


right-store-prefix-liftᵀ : RightStorePrefixLiftᵀ
right-store-prefix-liftᵀ = right-store-prefix-lift-proofᵀ
