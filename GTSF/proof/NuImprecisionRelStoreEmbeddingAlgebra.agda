module proof.NuImprecisionRelStoreEmbeddingAlgebra where

-- File Charter:
--   * Proves prefix restriction and composition for relational-store
--     embeddings.
--   * Provides the focused algebra needed to compose weak-result lineage.
--   * Contains no simulation result, catch-up, or semantic dispatcher proof.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; lift-left-store-[]
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; lift-left-store-∷
  ; lift-right-store-[]
  ; lift-right-store-left
  ; lift-right-store-link
  ; lift-right-store-right
  ; lift-right-store-∷
  ; lift-store-[]
  ; lift-store-left
  ; lift-store-link
  ; lift-store-right
  ; lift-store-∷
  ; store-left
  ; store-link
  ; store-matched
  ; store-right
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
open import Types using (Renameᵗ; renameᵗ)
open import proof.NuImprecisionRelStoreEmbeddingDef
open import proof.TypeProperties using
  (rename-cong; renameᵗ-compose; renameᵗ-id)


rel-store-embedding-reflⁱ :
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RelStoreEmbeddingⁱ (λ α → α) (λ β → β) ρ ρ
rel-store-embedding-reflⁱ {ρ = []} =
  rel-store-embedding-[]
rel-store-embedding-reflⁱ
    {ρ = store-matched α A β B p ∷ ρ} =
  rel-store-embedding-matched
    refl (sym (renameᵗ-id A)) refl (sym (renameᵗ-id B))
    rel-store-embedding-reflⁱ
rel-store-embedding-reflⁱ
    {ρ = store-left α A hA ∷ ρ} =
  rel-store-embedding-left
    refl (sym (renameᵗ-id A)) rel-store-embedding-reflⁱ
rel-store-embedding-reflⁱ
    {ρ = store-right β B hB ∷ ρ} =
  rel-store-embedding-right
    refl (sym (renameᵗ-id B)) rel-store-embedding-reflⁱ
rel-store-embedding-reflⁱ
    {ρ = store-link α A β B p ∷ ρ} =
  rel-store-embedding-link
    refl (sym (renameᵗ-id A)) refl (sym (renameᵗ-id B))
    rel-store-embedding-reflⁱ


lift-store-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  LiftStoreⁱ Ψ ρ ρ′ →
  RelStoreEmbeddingⁱ suc suc ρ ρ′
lift-store-embeddingⁱ lift-store-[] =
  rel-store-embedding-[]
lift-store-embeddingⁱ (lift-store-∷ liftρ) =
  rel-store-embedding-matched refl refl refl refl
    (lift-store-embeddingⁱ liftρ)
lift-store-embeddingⁱ (lift-store-left liftρ) =
  rel-store-embedding-left refl refl
    (lift-store-embeddingⁱ liftρ)
lift-store-embeddingⁱ (lift-store-right liftρ) =
  rel-store-embedding-right refl refl
    (lift-store-embeddingⁱ liftρ)
lift-store-embeddingⁱ (lift-store-link liftρ) =
  rel-store-embedding-link refl refl refl refl
    (lift-store-embeddingⁱ liftρ)


lift-left-store-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ (suc Δᴸ) Δᴿ} →
  LiftLeftStoreⁱ Ψ ρ ρ′ →
  RelStoreEmbeddingⁱ suc (λ β → β) ρ ρ′
lift-left-store-embeddingⁱ lift-left-store-[] =
  rel-store-embedding-[]
lift-left-store-embeddingⁱ
    (lift-left-store-∷ {B = B} liftρ) =
  rel-store-embedding-matched
    refl refl refl (sym (renameᵗ-id B))
    (lift-left-store-embeddingⁱ liftρ)
lift-left-store-embeddingⁱ (lift-left-store-left liftρ) =
  rel-store-embedding-left refl refl
    (lift-left-store-embeddingⁱ liftρ)
lift-left-store-embeddingⁱ
    (lift-left-store-right {B = B} liftρ) =
  rel-store-embedding-right refl (sym (renameᵗ-id B))
    (lift-left-store-embeddingⁱ liftρ)
lift-left-store-embeddingⁱ
    (lift-left-store-link {B = B} liftρ) =
  rel-store-embedding-link
    refl refl refl (sym (renameᵗ-id B))
    (lift-left-store-embeddingⁱ liftρ)


lift-right-store-embeddingⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp Ψ Δᴸ (suc Δᴿ)} →
  LiftRightStoreⁱ Ψ ρ ρ′ →
  RelStoreEmbeddingⁱ (λ α → α) suc ρ ρ′
lift-right-store-embeddingⁱ lift-right-store-[] =
  rel-store-embedding-[]
lift-right-store-embeddingⁱ
    (lift-right-store-∷ {A = A} liftρ) =
  rel-store-embedding-matched
    refl (sym (renameᵗ-id A)) refl refl
    (lift-right-store-embeddingⁱ liftρ)
lift-right-store-embeddingⁱ
    (lift-right-store-left {A = A} liftρ) =
  rel-store-embedding-left refl (sym (renameᵗ-id A))
    (lift-right-store-embeddingⁱ liftρ)
lift-right-store-embeddingⁱ (lift-right-store-right liftρ) =
  rel-store-embedding-right refl refl
    (lift-right-store-embeddingⁱ liftρ)
lift-right-store-embeddingⁱ
    (lift-right-store-link {A = A} liftρ) =
  rel-store-embedding-link
    refl (sym (renameᵗ-id A)) refl refl
    (lift-right-store-embeddingⁱ liftρ)


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
