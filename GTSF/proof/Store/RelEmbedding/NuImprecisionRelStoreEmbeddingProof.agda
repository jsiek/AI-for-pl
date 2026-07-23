module proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingProof where

-- File Charter:
--   * Transports stored or linked correspondence through a relational-store
--     embedding.
--   * Keeps membership-search helpers private and exports one theorem.
--   * Contains no simulation, catch-up, or result-lineage construction.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import NuTermImprecision using
  ( StoreImp
  ; StoreCorresponds
  ; correspondence-stored
  ; correspondence-linked
  ; store-matched
  ; store-link
  )
open import Types using (renameᵗ)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef


private
  rel-store-embedding-matched∈ⁱ :
    ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
      {α A β B p} →
    RelStoreEmbeddingⁱ τ σ ρ ρ′ →
    store-matched α A β B p ∈ ρ →
    ∃[ α′ ] ∃[ A′ ] ∃[ β′ ] ∃[ B′ ] ∃[ p′ ]
      (α′ ≡ τ α × A′ ≡ renameᵗ τ A ×
       β′ ≡ σ β × B′ ≡ renameᵗ σ B ×
       store-matched α′ A′ β′ B′ p′ ∈ ρ′)
  rel-store-embedding-matched∈ⁱ rel-store-embedding-[] ()
  rel-store-embedding-matched∈ⁱ
      (rel-store-embedding-matched
        {p′ = p′} eqα eqA eqβ eqB emb) (here refl) =
    _ , _ , _ , _ , p′ , eqα , eqA , eqβ , eqB , here refl
  rel-store-embedding-matched∈ⁱ
      (rel-store-embedding-matched eqα eqA eqβ eqB emb) (there p∈) =
    let α′ , A′ , β′ , B′ , p′ ,
          eqα′ , eqA′ , eqβ′ , eqB′ , p∈′ =
          rel-store-embedding-matched∈ⁱ emb p∈ in
    α′ , A′ , β′ , B′ , p′ ,
    eqα′ , eqA′ , eqβ′ , eqB′ , there p∈′
  rel-store-embedding-matched∈ⁱ
      (rel-store-embedding-left eqα eqA emb) (here ())
  rel-store-embedding-matched∈ⁱ
      (rel-store-embedding-left eqα eqA emb) (there p∈) =
    let α′ , A′ , β′ , B′ , p′ ,
          eqα′ , eqA′ , eqβ′ , eqB′ , p∈′ =
          rel-store-embedding-matched∈ⁱ emb p∈ in
    α′ , A′ , β′ , B′ , p′ ,
    eqα′ , eqA′ , eqβ′ , eqB′ , there p∈′
  rel-store-embedding-matched∈ⁱ
      (rel-store-embedding-right eqβ eqB emb) (here ())
  rel-store-embedding-matched∈ⁱ
      (rel-store-embedding-right eqβ eqB emb) (there p∈) =
    let α′ , A′ , β′ , B′ , p′ ,
          eqα′ , eqA′ , eqβ′ , eqB′ , p∈′ =
          rel-store-embedding-matched∈ⁱ emb p∈ in
    α′ , A′ , β′ , B′ , p′ ,
    eqα′ , eqA′ , eqβ′ , eqB′ , there p∈′
  rel-store-embedding-matched∈ⁱ
      (rel-store-embedding-link eqα eqA eqβ eqB emb) (here ())
  rel-store-embedding-matched∈ⁱ
      (rel-store-embedding-link eqα eqA eqβ eqB emb) (there p∈) =
    let α′ , A′ , β′ , B′ , p′ ,
          eqα′ , eqA′ , eqβ′ , eqB′ , p∈′ =
          rel-store-embedding-matched∈ⁱ emb p∈ in
    α′ , A′ , β′ , B′ , p′ ,
    eqα′ , eqA′ , eqβ′ , eqB′ , there p∈′

  rel-store-embedding-link∈ⁱ :
    ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
      {α A β B p} →
    RelStoreEmbeddingⁱ τ σ ρ ρ′ →
    store-link α A β B p ∈ ρ →
    ∃[ α′ ] ∃[ A′ ] ∃[ β′ ] ∃[ B′ ] ∃[ p′ ]
      (α′ ≡ τ α × A′ ≡ renameᵗ τ A ×
       β′ ≡ σ β × B′ ≡ renameᵗ σ B ×
       store-link α′ A′ β′ B′ p′ ∈ ρ′)
  rel-store-embedding-link∈ⁱ rel-store-embedding-[] ()
  rel-store-embedding-link∈ⁱ
      (rel-store-embedding-matched eqα eqA eqβ eqB emb) (here ())
  rel-store-embedding-link∈ⁱ
      (rel-store-embedding-matched eqα eqA eqβ eqB emb) (there p∈) =
    let α′ , A′ , β′ , B′ , p′ ,
          eqα′ , eqA′ , eqβ′ , eqB′ , p∈′ =
          rel-store-embedding-link∈ⁱ emb p∈ in
    α′ , A′ , β′ , B′ , p′ ,
    eqα′ , eqA′ , eqβ′ , eqB′ , there p∈′
  rel-store-embedding-link∈ⁱ
      (rel-store-embedding-left eqα eqA emb) (here ())
  rel-store-embedding-link∈ⁱ
      (rel-store-embedding-left eqα eqA emb) (there p∈) =
    let α′ , A′ , β′ , B′ , p′ ,
          eqα′ , eqA′ , eqβ′ , eqB′ , p∈′ =
          rel-store-embedding-link∈ⁱ emb p∈ in
    α′ , A′ , β′ , B′ , p′ ,
    eqα′ , eqA′ , eqβ′ , eqB′ , there p∈′
  rel-store-embedding-link∈ⁱ
      (rel-store-embedding-right eqβ eqB emb) (here ())
  rel-store-embedding-link∈ⁱ
      (rel-store-embedding-right eqβ eqB emb) (there p∈) =
    let α′ , A′ , β′ , B′ , p′ ,
          eqα′ , eqA′ , eqβ′ , eqB′ , p∈′ =
          rel-store-embedding-link∈ⁱ emb p∈ in
    α′ , A′ , β′ , B′ , p′ ,
    eqα′ , eqA′ , eqβ′ , eqB′ , there p∈′
  rel-store-embedding-link∈ⁱ
      (rel-store-embedding-link
        {p′ = p′} eqα eqA eqβ eqB emb) (here refl) =
    _ , _ , _ , _ , p′ , eqα , eqA , eqβ , eqB , here refl
  rel-store-embedding-link∈ⁱ
      (rel-store-embedding-link eqα eqA eqβ eqB emb) (there p∈) =
    let α′ , A′ , β′ , B′ , p′ ,
          eqα′ , eqA′ , eqβ′ , eqB′ , p∈′ =
          rel-store-embedding-link∈ⁱ emb p∈ in
    α′ , A′ , β′ , B′ , p′ ,
    eqα′ , eqA′ , eqβ′ , eqB′ , there p∈′


rel-store-embedding-correspondenceⁱ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {α A β B p} →
  RelStoreEmbeddingⁱ τ σ ρ ρ′ →
  StoreCorresponds ρ α A β B p →
  ∃[ α′ ] ∃[ A′ ] ∃[ β′ ] ∃[ B′ ] ∃[ p′ ]
    (α′ ≡ τ α × A′ ≡ renameᵗ τ A ×
     β′ ≡ σ β × B′ ≡ renameᵗ σ B ×
     StoreCorresponds ρ′ α′ A′ β′ B′ p′)
rel-store-embedding-correspondenceⁱ emb
    (correspondence-stored p∈) =
  let α′ , A′ , β′ , B′ , p′ , eqα , eqA , eqβ , eqB , p∈′ =
        rel-store-embedding-matched∈ⁱ emb p∈ in
  α′ , A′ , β′ , B′ , p′ , eqα , eqA , eqβ , eqB ,
  correspondence-stored p∈′
rel-store-embedding-correspondenceⁱ emb
    (correspondence-linked p∈) =
  let α′ , A′ , β′ , B′ , p′ , eqα , eqA , eqβ , eqB , p∈′ =
        rel-store-embedding-link∈ⁱ emb p∈ in
  α′ , A′ , β′ , B′ , p′ , eqα , eqA , eqβ , eqB ,
  correspondence-linked p∈′
