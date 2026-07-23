module proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef where

-- File Charter:
--   * Defines structural embeddings between relational stores.
--   * Records renaming of names and endpoint types for every old entry.
--   * Is the small stable statement dependency for store-lineage results.
--   * Contains no simulation result, catch-up, or correspondence proof.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)

open import NuTermImprecision using
  ( StoreImp
  ; store-matched
  ; store-left
  ; store-right
  ; store-link
  )
open import Types using (Renameᵗ; renameᵗ)


data RelStoreEmbeddingⁱ
    {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    (τ σ : Renameᵗ) :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Ψ Θᴸ Θᴿ → Set₁ where
  rel-store-embedding-[] :
    RelStoreEmbeddingⁱ τ σ [] []

  rel-store-embedding-matched :
    ∀ {ρ ρ′ α α′ A A′ β β′ B B′ p p′} →
    α′ ≡ τ α → A′ ≡ renameᵗ τ A →
    β′ ≡ σ β → B′ ≡ renameᵗ σ B →
    RelStoreEmbeddingⁱ τ σ ρ ρ′ →
    RelStoreEmbeddingⁱ τ σ
      (store-matched α A β B p ∷ ρ)
      (store-matched α′ A′ β′ B′ p′ ∷ ρ′)

  rel-store-embedding-left :
    ∀ {ρ ρ′ α α′ A A′ hA hA′} →
    α′ ≡ τ α → A′ ≡ renameᵗ τ A →
    RelStoreEmbeddingⁱ τ σ ρ ρ′ →
    RelStoreEmbeddingⁱ τ σ
      (store-left α A hA ∷ ρ)
      (store-left α′ A′ hA′ ∷ ρ′)

  rel-store-embedding-right :
    ∀ {ρ ρ′ β β′ B B′ hB hB′} →
    β′ ≡ σ β → B′ ≡ renameᵗ σ B →
    RelStoreEmbeddingⁱ τ σ ρ ρ′ →
    RelStoreEmbeddingⁱ τ σ
      (store-right β B hB ∷ ρ)
      (store-right β′ B′ hB′ ∷ ρ′)

  rel-store-embedding-link :
    ∀ {ρ ρ′ α α′ A A′ β β′ B B′ p p′} →
    α′ ≡ τ α → A′ ≡ renameᵗ τ A →
    β′ ≡ σ β → B′ ≡ renameᵗ σ B →
    RelStoreEmbeddingⁱ τ σ ρ ρ′ →
    RelStoreEmbeddingⁱ τ σ
      (store-link α A β B p ∷ ρ)
      (store-link α′ A′ β′ B′ p′ ∷ ρ′)
