module proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefixAlgebra where

-- File Charter:
--   * Proves composition and relational-embedding inversion for target-only
--     relational-store prefixes.
--   * Supplies the store algebra needed when target-allocation catch-up
--     results are composed.
--   * Contains no simulation result, term relation, postulate, hole,
--     permissive option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong₂; trans)

open import NuTermImprecision using (leftStoreⁱ)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef using
  ( RelStoreEmbeddingⁱ
  ; rel-store-embedding-[]
  ; rel-store-embedding-left
  ; rel-store-embedding-link
  ; rel-store-embedding-matched
  ; rel-store-embedding-right
  )
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  ( RightOnlyStoreImpPrefix
  ; right-only-prefix-refl
  ; right-only-prefix-right
  )
open import proof.Core.Properties.TypeProperties using (renameᵗ-id)


right-only-store-prefix-transⁱ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ₁ ρ₂} →
  RightOnlyStoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ₁ →
  RightOnlyStoreImpPrefix ρ₁ ρ₂ →
  RightOnlyStoreImpPrefix ρ₀ ρ₂
right-only-store-prefix-transⁱ prefix₀₁ right-only-prefix-refl =
  prefix₀₁
right-only-store-prefix-transⁱ prefix₀₁
    (right-only-prefix-right prefix₁₂) =
  right-only-prefix-right
    (right-only-store-prefix-transⁱ prefix₀₁ prefix₁₂)


rel-store-embedding-right-only-prefix-invⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {ρ₀ ρ⁺ ρ′⁺} →
  RightOnlyStoreImpPrefix
    {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
  RelStoreEmbeddingⁱ
    {Ψ = Ψ} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
    τ σ ρ⁺ ρ′⁺ →
  Σ[ ρ′₀ ∈ _ ]
    RelStoreEmbeddingⁱ τ σ ρ₀ ρ′₀ ×
    RightOnlyStoreImpPrefix ρ′₀ ρ′⁺
rel-store-embedding-right-only-prefix-invⁱ
    right-only-prefix-refl embedding =
  _ , embedding , right-only-prefix-refl
rel-store-embedding-right-only-prefix-invⁱ
    (right-only-prefix-right prefix)
    (rel-store-embedding-right eqβ eqB embedding)
    with rel-store-embedding-right-only-prefix-invⁱ prefix embedding
rel-store-embedding-right-only-prefix-invⁱ
    (right-only-prefix-right prefix)
    (rel-store-embedding-right eqβ eqB embedding)
    | ρ′₀ , embedding′ , prefix′ =
  ρ′₀ , embedding′ , right-only-prefix-right prefix′


right-only-store-prefix-left-storeⁱ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺} →
  RightOnlyStoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
  leftStoreⁱ ρ⁺ ≡ leftStoreⁱ ρ₀
right-only-store-prefix-left-storeⁱ right-only-prefix-refl =
  refl
right-only-store-prefix-left-storeⁱ
    (right-only-prefix-right prefix) =
  right-only-store-prefix-left-storeⁱ prefix


identity-left-store-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ σ} {ρ ρ′} →
  RelStoreEmbeddingⁱ
    {Φ} {Ψ} {Δᴸ} {Δᴿ} {Θᴸ} {Θᴿ}
    (λ α → α) σ ρ ρ′ →
  leftStoreⁱ ρ′ ≡ leftStoreⁱ ρ
identity-left-store-embeddingⁱ
    rel-store-embedding-[] =
  refl
identity-left-store-embeddingⁱ
    (rel-store-embedding-matched eqα eqA eqβ eqB embedding) =
  cong₂ _∷_
    (cong₂ _,_ eqα (trans eqA (renameᵗ-id _)))
    (identity-left-store-embeddingⁱ embedding)
identity-left-store-embeddingⁱ
    (rel-store-embedding-left eqα eqA embedding) =
  cong₂ _∷_
    (cong₂ _,_ eqα (trans eqA (renameᵗ-id _)))
    (identity-left-store-embeddingⁱ embedding)
identity-left-store-embeddingⁱ
    (rel-store-embedding-right eqβ eqB embedding) =
  identity-left-store-embeddingⁱ embedding
identity-left-store-embeddingⁱ
    (rel-store-embedding-link eqα eqA eqβ eqB embedding) =
  identity-left-store-embeddingⁱ embedding


right-only-lineage-left-storeⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ σ}
    {ρ₀ ρlineage ρbase} →
  RelStoreEmbeddingⁱ
    {Φ} {Ψ} {Δᴸ} {Δᴿ} {Θᴸ} {Θᴿ}
    (λ α → α) σ ρ₀ ρlineage →
  RightOnlyStoreImpPrefix ρlineage ρbase →
  leftStoreⁱ ρbase ≡ leftStoreⁱ ρ₀
right-only-lineage-left-storeⁱ embedding prefix =
  trans
    (right-only-store-prefix-left-storeⁱ prefix)
    (identity-left-store-embeddingⁱ embedding)
