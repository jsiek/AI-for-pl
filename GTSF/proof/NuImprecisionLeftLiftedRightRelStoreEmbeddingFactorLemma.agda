module
  proof.NuImprecisionLeftLiftedRightRelStoreEmbeddingFactorLemma
  where

-- File Charter:
--   * Exposes the canonical inverse factorization theorem for target-only
--     relational-store embeddings beneath source-only lifts.
--   * Keeps callers independent of the structural worker proof.
--   * Contains no term relation, postulate, hole, permissive option,
--     termination bypass, or broad simulation import.

open import
  proof.NuImprecisionLeftLiftedRightRelStoreEmbeddingFactorDef
  using (LeftLiftedRightRelStoreEmbeddingFactorᵀ)
open import
  proof.NuImprecisionLeftLiftedRightRelStoreEmbeddingFactorProof
  using (left-lifted-right-rel-store-embedding-factor-proofᵀ)


left-lifted-right-rel-store-embedding-factorᵀ :
  LeftLiftedRightRelStoreEmbeddingFactorᵀ
left-lifted-right-rel-store-embedding-factorᵀ liftρ emb =
  left-lifted-right-rel-store-embedding-factor-proofᵀ
    liftρ emb
