module
  proof.Left.LiftedStore.NuImprecisionLeftLiftedRightRelStoreEmbeddingFactorProof
  where

-- File Charter:
--   * Proves inverse factorization of target-only relational-store
--     embeddings beneath source-only lifts by exhaustive structural
--     recursion.
--   * Drops the fresh source name from matched and link evidence while
--     preserving target endpoint renaming exactly.
--   * Contains no term relation, postulate, hole, catch-all, permissive
--     option, termination bypass, or broad simulation import.

open import Data.List using ([]; _∷_)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (refl; subst; sym; trans)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  ( lift-left-store-[]
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; lift-left-store-∷
  ; store-left
  ; store-link
  ; store-matched
  ; store-right
  )
open import Types using (⇑ᵗ)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (open-unusedᵢ)
open import
  proof.Left.LiftedStore.NuImprecisionLeftLiftedRightRelStoreEmbeddingFactorDef
  using (LeftLiftedRightRelStoreEmbeddingFactorᵀ)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef using
  ( rel-store-embedding-[]
  ; rel-store-embedding-left
  ; rel-store-embedding-link
  ; rel-store-embedding-matched
  ; rel-store-embedding-right
  )
open import proof.Core.Properties.TypeProperties using
  ( occurs-raise-fresh
  ; renameᵗ-id
  ; renameᵗ-single-suc-cancel
  )


left-lifted-right-rel-store-embedding-factor-proofᵀ :
  LeftLiftedRightRelStoreEmbeddingFactorᵀ
left-lifted-right-rel-store-embedding-factor-proofᵀ
    lift-left-store-[] rel-store-embedding-[] =
  [] , lift-left-store-[] , rel-store-embedding-[]
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-∷ {A = A} {p′ = pᴸ} liftρ)
    (rel-store-embedding-matched
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p′ = p′ᴸ}
      eqα eqA eqβ eqB emb)
    with eqα | trans eqA (renameᵗ-id (⇑ᵗ A))
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-∷ {A = A} {p′ = pᴸ} liftρ)
    (rel-store-embedding-matched
      {β′ = β′} {B′ = B′} {p′ = p′ᴸ}
      eqα eqA eqβ eqB emb)
    | refl | refl
    with left-lifted-right-rel-store-embedding-factor-proofᵀ
      liftρ emb
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-∷ {A = A} {p′ = pᴸ} liftρ)
    (rel-store-embedding-matched
      {β′ = β′} {B′ = B′} {p′ = p′ᴸ}
      eqα eqA eqβ eqB emb)
    | refl | refl
    | ρ′ , liftρ′ , emb′ =
  store-matched _ A β′ B′ base-p ∷ ρ′ ,
  lift-left-store-∷ liftρ′ ,
  rel-store-embedding-matched
    refl (sym (renameᵗ-id A)) eqβ eqB emb′
  where
  base-p =
    subst
      (λ S → _ ∣ _ ⊢ S ⊑ B′ ⊣ _)
      (renameᵗ-single-suc-cancel zero A)
      (open-unusedᵢ (occurs-raise-fresh zero A) p′ᴸ)
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-left {A = A} {hA = hA} liftρ)
    (rel-store-embedding-left
      {α′ = α′} {A′ = A′} eqα eqA emb)
    with eqα | trans eqA (renameᵗ-id (⇑ᵗ A))
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-left {A = A} {hA = hA} liftρ)
    (rel-store-embedding-left eqα eqA emb)
    | refl | refl
    with left-lifted-right-rel-store-embedding-factor-proofᵀ
      liftρ emb
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-left {A = A} {hA = hA} liftρ)
    (rel-store-embedding-left eqα eqA emb)
    | refl | refl
    | ρ′ , liftρ′ , emb′ =
  store-left _ A hA ∷ ρ′ ,
  lift-left-store-left liftρ′ ,
  rel-store-embedding-left
    refl (sym (renameᵗ-id A)) emb′
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-right liftρ)
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    with left-lifted-right-rel-store-embedding-factor-proofᵀ
      liftρ emb
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-right liftρ)
    (rel-store-embedding-right
      {β′ = β′} {B′ = B′} {hB′ = hB′} eqβ eqB emb)
    | ρ′ , liftρ′ , emb′ =
  store-right β′ B′ hB′ ∷ ρ′ ,
  lift-left-store-right liftρ′ ,
  rel-store-embedding-right eqβ eqB emb′
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-link {A = A} {p′ = pᴸ} liftρ)
    (rel-store-embedding-link
      {α′ = α′} {A′ = A′} {β′ = β′} {B′ = B′}
      {p′ = p′ᴸ}
      eqα eqA eqβ eqB emb)
    with eqα | trans eqA (renameᵗ-id (⇑ᵗ A))
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-link {A = A} {p′ = pᴸ} liftρ)
    (rel-store-embedding-link
      {β′ = β′} {B′ = B′} {p′ = p′ᴸ}
      eqα eqA eqβ eqB emb)
    | refl | refl
    with left-lifted-right-rel-store-embedding-factor-proofᵀ
      liftρ emb
left-lifted-right-rel-store-embedding-factor-proofᵀ
    (lift-left-store-link {A = A} {p′ = pᴸ} liftρ)
    (rel-store-embedding-link
      {β′ = β′} {B′ = B′} {p′ = p′ᴸ}
      eqα eqA eqβ eqB emb)
    | refl | refl
    | ρ′ , liftρ′ , emb′ =
  store-link _ A β′ B′ base-p ∷ ρ′ ,
  lift-left-store-link liftρ′ ,
  rel-store-embedding-link
    refl (sym (renameᵗ-id A)) eqβ eqB emb′
  where
  base-p =
    subst
      (λ S → _ ∣ _ ⊢ S ⊑ B′ ⊣ _)
      (renameᵗ-single-suc-cancel zero A)
      (open-unusedᵢ (occurs-raise-fresh zero A) p′ᴸ)
