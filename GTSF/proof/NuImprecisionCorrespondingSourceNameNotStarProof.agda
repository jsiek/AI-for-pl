module proof.NuImprecisionCorrespondingSourceNameNotStarProof where

-- File Charter:
--   * Proves the world-invariant corollary that a source name participating in
--     StoreCorresponds cannot also be marked source-only in the same context.
--   * Uses the WorldCoherent converse field and SourceNameExclusive directly.
--   * Exports only corresponding-source-name-not-star-proofᵀ.

open import proof.NuImprecisionCorrespondingSourceNameNotStarDef using
  (CorrespondingSourceNameNotStarᵀ)
open import proof.NuImprecisionWorldCoherenceDef using
  (corresponds-idˣ)


corresponding-source-name-not-star-proofᵀ : CorrespondingSourceNameNotStarᵀ
corresponding-source-name-not-star-proofᵀ coherent exclusive corresponds star∈ =
  exclusive star∈ (corresponds-idˣ coherent corresponds)
