module proof.NuImprecisionRelStoreEmbeddingAlgebra where

-- File Charter:
--   * Proves prefix restriction and composition for relational-store
--     embeddings.
--   * Provides the focused algebra needed to compose weak-result lineage.
--   * Contains no simulation result, catch-up, or semantic dispatcher proof.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
open import Types using (Renameᵗ; renameᵗ)
open import proof.NuImprecisionRelStoreEmbeddingDef
open import proof.TypeProperties using (rename-cong; renameᵗ-compose)


rel-store-embedding-congⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ τ′ σ′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ Θᴸ Θᴿ} →
  (∀ α → τ α ≡ τ′ α) →
  (∀ β → σ β ≡ σ′ β) →
  RelStoreEmbeddingⁱ τ σ ρ ρ′ →
  RelStoreEmbeddingⁱ τ′ σ′ ρ ρ′
rel-store-embedding-congⁱ eqτ eqσ rel-store-embedding-[] =
  rel-store-embedding-[]
rel-store-embedding-congⁱ eqτ eqσ
    (rel-store-embedding-matched eqα eqA eqβ eqB emb) =
  rel-store-embedding-matched
    (trans eqα (eqτ _))
    (trans eqA (rename-cong eqτ _))
    (trans eqβ (eqσ _))
    (trans eqB (rename-cong eqσ _))
    (rel-store-embedding-congⁱ eqτ eqσ emb)
rel-store-embedding-congⁱ eqτ eqσ
    (rel-store-embedding-left eqα eqA emb) =
  rel-store-embedding-left
    (trans eqα (eqτ _))
    (trans eqA (rename-cong eqτ _))
    (rel-store-embedding-congⁱ eqτ eqσ emb)
rel-store-embedding-congⁱ eqτ eqσ
    (rel-store-embedding-right eqβ eqB emb) =
  rel-store-embedding-right
    (trans eqβ (eqσ _))
    (trans eqB (rename-cong eqσ _))
    (rel-store-embedding-congⁱ eqτ eqσ emb)
rel-store-embedding-congⁱ eqτ eqσ
    (rel-store-embedding-link eqα eqA eqβ eqB emb) =
  rel-store-embedding-link
    (trans eqα (eqτ _))
    (trans eqA (rename-cong eqτ _))
    (trans eqβ (eqσ _))
    (trans eqB (rename-cong eqσ _))
    (rel-store-embedding-congⁱ eqτ eqσ emb)


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
    (rel-store-embedding-matched eqα eqA eqβ eqB emb)
    with rel-store-embedding-prefix-invⁱ prefix emb
rel-store-embedding-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-embedding-matched eqα eqA eqβ eqB emb)
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
    (rel-store-embedding-link eqα eqA eqβ eqB emb)
    with rel-store-embedding-prefix-invⁱ prefix emb
rel-store-embedding-prefix-invⁱ (prefix-∷ⁱ prefix)
    (rel-store-embedding-link eqα eqA eqβ eqB emb)
    | ρ₀′ , emb₀ , prefix′ =
  ρ₀′ , emb₀ , prefix-∷ⁱ prefix′


private
  renamed-name-compose :
    ∀ {τ υ : Renameᵗ} {α α₁ α₂} →
    α₁ ≡ τ α →
    α₂ ≡ υ α₁ →
    α₂ ≡ υ (τ α)
  renamed-name-compose {τ = τ} {υ = υ} eq₁ eq₂ =
    trans eq₂ (cong υ eq₁)

  renamed-type-compose :
    ∀ (τ υ : Renameᵗ) {A A₁ A₂} →
    A₁ ≡ renameᵗ τ A →
    A₂ ≡ renameᵗ υ A₁ →
    A₂ ≡ renameᵗ (λ X → υ (τ X)) A
  renamed-type-compose τ υ {A = A} eq₁ eq₂ =
    trans eq₂
      (trans (cong (renameᵗ υ) eq₁) (renameᵗ-compose τ υ A))


rel-store-embedding-composeⁱ :
  ∀ {Φ Ψ Ω Δᴸ Δᴿ Θᴸ Θᴿ Ξᴸ Ξᴿ τ σ υ ω}
    {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₁ : StoreImp Ψ Θᴸ Θᴿ}
    {ρ₂ : StoreImp Ω Ξᴸ Ξᴿ} →
  RelStoreEmbeddingⁱ τ σ ρ₀ ρ₁ →
  RelStoreEmbeddingⁱ υ ω ρ₁ ρ₂ →
  RelStoreEmbeddingⁱ
    (λ X → υ (τ X)) (λ X → ω (σ X)) ρ₀ ρ₂
rel-store-embedding-composeⁱ
    rel-store-embedding-[] rel-store-embedding-[] =
  rel-store-embedding-[]
rel-store-embedding-composeⁱ
    {τ = τ} {σ = σ} {υ = υ} {ω = ω}
    (rel-store-embedding-matched
      {A = A} {B = B} eqα₁ eqA₁ eqβ₁ eqB₁ emb₁)
    (rel-store-embedding-matched eqα₂ eqA₂ eqβ₂ eqB₂ emb₂) =
  rel-store-embedding-matched
    (renamed-name-compose {τ = τ} {υ = υ} eqα₁ eqα₂)
    (renamed-type-compose τ υ {A = A} eqA₁ eqA₂)
    (renamed-name-compose {τ = σ} {υ = ω} eqβ₁ eqβ₂)
    (renamed-type-compose σ ω {A = B} eqB₁ eqB₂)
    (rel-store-embedding-composeⁱ emb₁ emb₂)
rel-store-embedding-composeⁱ
    {τ = τ} {υ = υ}
    (rel-store-embedding-left {A = A} eqα₁ eqA₁ emb₁)
    (rel-store-embedding-left eqα₂ eqA₂ emb₂) =
  rel-store-embedding-left
    (renamed-name-compose {τ = τ} {υ = υ} eqα₁ eqα₂)
    (renamed-type-compose τ υ {A = A} eqA₁ eqA₂)
    (rel-store-embedding-composeⁱ emb₁ emb₂)
rel-store-embedding-composeⁱ
    {σ = σ} {ω = ω}
    (rel-store-embedding-right {B = B} eqβ₁ eqB₁ emb₁)
    (rel-store-embedding-right eqβ₂ eqB₂ emb₂) =
  rel-store-embedding-right
    (renamed-name-compose {τ = σ} {υ = ω} eqβ₁ eqβ₂)
    (renamed-type-compose σ ω {A = B} eqB₁ eqB₂)
    (rel-store-embedding-composeⁱ emb₁ emb₂)
rel-store-embedding-composeⁱ
    {τ = τ} {σ = σ} {υ = υ} {ω = ω}
    (rel-store-embedding-link
      {A = A} {B = B} eqα₁ eqA₁ eqβ₁ eqB₁ emb₁)
    (rel-store-embedding-link eqα₂ eqA₂ eqβ₂ eqB₂ emb₂) =
  rel-store-embedding-link
    (renamed-name-compose {τ = τ} {υ = υ} eqα₁ eqα₂)
    (renamed-type-compose τ υ {A = A} eqA₁ eqA₂)
    (renamed-name-compose {τ = σ} {υ = ω} eqβ₁ eqβ₂)
    (renamed-type-compose σ ω {A = B} eqB₁ eqB₂)
    (rel-store-embedding-composeⁱ emb₁ emb₂)
