module
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingPrefixProof
  where

-- File Charter:
--   * Proves inversion of a live relational-store prefix through a structural
--     relational-store embedding.
--   * Isolates the sole store-prefix dependency from the otherwise
--     term-relation-independent store-embedding algebra.
--   * Contains no simulation result, postulate, hole, permissive option,
--     termination bypass, or catch-all clause.

open import Data.Product using (_×_; _,_; ∃-syntax)

open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using
  (StoreImpPrefix; prefix-reflⁱ; prefix-∷ⁱ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
open import Types using (Renameᵗ)


rel-store-embedding-prefix-invⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′⁺ : StoreImp Ψ Θᴸ Θᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RelStoreEmbeddingⁱ τ σ ρ⁺ ρ′⁺ →
  ∃[ ρ₀′ ]
    RelStoreEmbeddingⁱ τ σ ρ₀ ρ₀′ ×
    StoreImpPrefix ρ₀′ ρ′⁺
rel-store-embedding-prefix-invⁱ prefix-reflⁱ emb =
  _ , emb , prefix-reflⁱ
rel-store-embedding-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-embedding-matched
      eqα eqA eqβ eqB shape-eq emb)
    with rel-store-embedding-prefix-invⁱ prefix emb
rel-store-embedding-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-embedding-matched
      eqα eqA eqβ eqB shape-eq emb)
    | ρ₀′ , emb₀ , prefix′ =
  ρ₀′ , emb₀ , prefix-∷ⁱ prefix′
rel-store-embedding-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-embedding-left eqα eqA emb)
    with rel-store-embedding-prefix-invⁱ prefix emb
rel-store-embedding-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-embedding-left eqα eqA emb)
    | ρ₀′ , emb₀ , prefix′ =
  ρ₀′ , emb₀ , prefix-∷ⁱ prefix′
rel-store-embedding-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-embedding-right eqβ eqB emb)
    with rel-store-embedding-prefix-invⁱ prefix emb
rel-store-embedding-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-embedding-right eqβ eqB emb)
    | ρ₀′ , emb₀ , prefix′ =
  ρ₀′ , emb₀ , prefix-∷ⁱ prefix′
rel-store-embedding-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-embedding-link
      eqα eqA eqβ eqB shape-eq emb)
    with rel-store-embedding-prefix-invⁱ prefix emb
rel-store-embedding-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-embedding-link
      eqα eqA eqβ eqB shape-eq emb)
    | ρ₀′ , emb₀ , prefix′ =
  ρ₀′ , emb₀ , prefix-∷ⁱ prefix′
