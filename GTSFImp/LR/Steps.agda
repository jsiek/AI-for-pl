module LR.Steps where

-- File Charter:
--   * Counted reduction for the logical relation (notes/logrel-dgg.md,
--     Section 6.2): `M —→ᵏ[ χs ] N` takes exactly k steps of
--     `_—→[_]_`, every step counted, pure or store-changing.
--   * A store is only its size: reduction never reads a store's
--     contents.  The store changes of a reduction give an
--     order-preserving embedding of the old store into the new one
--     (`embedᶜˢ`), along which a world is extended.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax)

open import Types
open import Consistency using (_↪ᵗ_; empty; keep; skip; id↪ᵗ; wk↪ᵗ)
open import CastTerms
open import Reduction
open import proof.DGG.CenterRename using (_∘↪_)

------------------------------------------------------------------------
-- Embeddings of stores
------------------------------------------------------------------------

-- the embedding of a store into the store after one change
embedᶜ : ∀ {Δ Δ′} → StoreChange Δ Δ′ → Δ ↪ᵗ Δ′
embedᶜ keep = id↪ᵗ
embedᶜ (bind A) = wk↪ᵗ

-- the embedding of a store into the store after a sequence of changes
embedᶜˢ : ∀ {Δ Δ′} → StoreChanges Δ Δ′ → Δ ↪ᵗ Δ′
embedᶜˢ [] = id↪ᵗ
embedᶜˢ (χ ∷ χs) = embedᶜˢ χs ∘↪ embedᶜ χ

------------------------------------------------------------------------
-- Counted reduction
------------------------------------------------------------------------

infix 2 _—→^_[_]_

-- exactly k steps
data _—→^_[_]_ : ∀ {Δ Δ′}
    → Term Δ → ℕ → StoreChanges Δ Δ′ → Term Δ′ → Set where

  none : ∀ {Δ} {M : Term Δ}
      ---------------------
    → M —→^ zero [ [] ] M

  more : ∀ {Δ Δ′ Δ″ k} {M : Term Δ} {N : Term Δ′} {P : Term Δ″}
      {χ : StoreChange Δ Δ′} {χs : StoreChanges Δ′ Δ″}
    → M —→[ χ ] N
    → N —→^ k [ χs ] P
      ------------------------------
    → M —→^ suc k [ χ ∷ χs ] P

-- M can take k steps (it has not stopped before them)
Runs : ∀ {Δ} → Term Δ → ℕ → Set
Runs {Δ} M k =
  Σ[ Δ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δ Δ′ ] Σ[ N ∈ Term Δ′ ]
    (M —→^ k [ χs ] N)

-- forgetting the count
steps→↠ : ∀ {Δ Δ′ k} {M : Term Δ} {χs : StoreChanges Δ Δ′} {N : Term Δ′}
  → M —→^ k [ χs ] N → M —↠[ χs ] N
steps→↠ none = ↠-refl
steps→↠ (more s ss) = ↠-step s (steps→↠ ss)
