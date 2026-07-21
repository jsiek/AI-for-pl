module proof.NuImprecisionLeftLiftPrefixBodyProof where

-- File Charter:
--   * Proves the canonical strict `LeftLiftPrefixBodyᵀ` contract.
--   * Reconstructs the source-left lift proof from low-level world-embedding
--     support without importing the broad simulation or source-bullet modules.
--   * Imports the generic no-runtime-bullet traversal from its focused owner.
--   * Contains only total proof terms, with no permissive options or dispatcher
--     logic.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import ImprecisionWf using (_ˣ⊑★; ⇑ᴸᵢ)
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; lift-left-store-[]
  ; lift-left-store-∷
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  )
open import NuTerms using (renameᵗᵐ)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import Relation.Binary.PropositionalEquality using (sym)
open import Types using (renameᵗ)
open import proof.MaximalLowerBoundsWf using
  (rename-assm²-source-νᵢ)
open import proof.NuImprecisionLeftLiftPrefixBodyDef using
  (LeftLiftPrefixBodyᵀ)
open import proof.NuImprecisionRelStoreEmbeddingDef using
  ( RelStoreEmbeddingⁱ
  ; rel-store-embedding-[]
  ; rel-store-embedding-left
  ; rel-store-embedding-link
  ; rel-store-embedding-matched
  ; rel-store-embedding-right
  )
open import proof.NuImprecisionSimulationCore using
  ( RelWorldEmbeddingⁱ
  ; castModeRenamer-id
  ; nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  ; rel-ctx-rename-[]
  ; rel-world-embedding
  )
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.NuImprecisionWorldEmbeddingNoBullet using
  (rel-world-embed-no•ᵀ)
open import proof.NuTermProperties using
  (renameᵗᵐ-id; renameᵗᵐ-preserves-No•)
open import proof.TypePreservation using
  (castModeRenamer-suc; term-weaken)
open import proof.TypeProperties using
  ( RenameLeftInverse-suc
  ; TyRenameWf-suc
  ; predᵗ
  ; renameᵗ-id
  )


private
  lift-left-store-rel-embeddingⁱ :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ} →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
    RelStoreEmbeddingⁱ suc (λ X → X) ρ ρ′
  lift-left-store-rel-embeddingⁱ lift-left-store-[] =
    rel-store-embedding-[]
  lift-left-store-rel-embeddingⁱ (lift-left-store-∷ liftρ) =
    rel-store-embedding-matched refl refl refl
      (sym (renameᵗ-id _)) (lift-left-store-rel-embeddingⁱ liftρ)
  lift-left-store-rel-embeddingⁱ (lift-left-store-left liftρ) =
    rel-store-embedding-left refl refl
      (lift-left-store-rel-embeddingⁱ liftρ)
  lift-left-store-rel-embeddingⁱ (lift-left-store-right liftρ) =
    rel-store-embedding-right refl (sym (renameᵗ-id _))
      (lift-left-store-rel-embeddingⁱ liftρ)
  lift-left-store-rel-embeddingⁱ (lift-left-store-link liftρ) =
    rel-store-embedding-link refl refl refl
      (sym (renameᵗ-id _)) (lift-left-store-rel-embeddingⁱ liftρ)

  left-lift-world-embeddingⁱ :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ} →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
    RelWorldEmbeddingⁱ suc (λ X → X) predᵗ (λ X → X)
      rename-assm²-source-νᵢ TyRenameWf-suc (λ X<Δ → X<Δ)
      {ρ = ρ} {ρ′ = ρ′} {γ = []} {γ′ = []}
  left-lift-world-embeddingⁱ liftρ =
    rel-world-embedding RenameLeftInverse-suc (λ X → refl)
      castModeRenamer-suc castModeRenamer-id
      (lift-left-store-rel-embeddingⁱ liftρ) rel-ctx-rename-[]


left-lift-prefix-body-proofᵀ : LeftLiftPrefixBodyᵀ
left-lift-prefix-body-proofᵀ {B = B} {L′ = L′}
    liftρ prefix noL noL′ L⊑L′ =
  allocation-prefixᵀ prefix body
    (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      noL↑ (nu-term-imprecision-source-typing body))
    (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      noL′ (nu-term-imprecision-target-typing body))
  where
  body =
    nu-term-imprecision-transport-termsᵀ refl (renameᵗᵐ-id L′)
      (nu-term-imprecision-transport-typesᵀ
        refl (renameᵗ-id B) refl
        (rel-world-embed-no•ᵀ
          (left-lift-world-embeddingⁱ liftρ) L⊑L′ noL noL′))
  noL↑ = renameᵗᵐ-preserves-No• suc noL
