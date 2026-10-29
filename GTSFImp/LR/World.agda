module LR.World where

-- File Charter:
--   * Kripke worlds for the logical relation (notes/logrel-dgg.md,
--     Section 6.11): the sizes of the two stores, and for each left
--     store variable a tag descriptor (`LR.Desc`).  Tags are syntax, so
--     worlds need no staging and live in `Set`.
--   * Extension `w′ ⊒ w` embeds both stores in order and keeps every
--     old tag, renamed.
--   * Relations relative to a store: a relation at each stage, applied
--     at any world together with embeddings of the store into the
--     world's stores (`RelΩ`).  This is how a leaf relation built in one
--     world is read in a later one.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ; id↪ᵗ)
open import CastTerms using (Term)
open import LR.Steps using (_∘ᵉ_)
open import LR.Desc

------------------------------------------------------------------------
-- Worlds
------------------------------------------------------------------------

record World : Set where
  constructor world
  field
    ΔL : TyCtx
    ΔR : TyCtx
    tag : TyVar ΔL → Tag ΔL ΔR

open World public

infix 4 _⊒_

-- w′ is a possible future of w
record _⊒_ (w′ w : World) : Set where
  constructor ext
  field
    ρL : ΔL w ↪ᵗ ΔL w′
    ρR : ΔR w ↪ᵗ ΔR w′
    tags≡ : ∀ X → tag w′ (toRenameᵗ ρL X) ≡ renameTag ρL ρR (tag w X)

open _⊒_ public

------------------------------------------------------------------------
-- Relations relative to a store
------------------------------------------------------------------------

-- a relation at each stage, read at any world through embeddings of the
-- stores ΔL, ΔR into the world's stores
RelΩ : TyCtx → TyCtx → Set₁
RelΩ ΔL₀ ΔR₀ = (k : ℕ) (w : World)
  → ΔL₀ ↪ᵗ ΔL w → ΔR₀ ↪ᵗ ΔR w
  → Term (ΔL w) → Term (ΔR w) → Set

-- moving a relation to a larger store
transportΩ : ∀ {ΔL₀ ΔR₀ ΔL₁ ΔR₁}
  → ΔL₀ ↪ᵗ ΔL₁ → ΔR₀ ↪ᵗ ΔR₁ → RelΩ ΔL₀ ΔR₀ → RelΩ ΔL₁ ΔR₁
transportΩ σL σR R k w τL τR = R k w (τL ∘ᵉ σL) (τR ∘ᵉ σR)

-- the trivial relation
⊤Ω : ∀ {ΔL₀ ΔR₀} → RelΩ ΔL₀ ΔR₀
⊤Ω k w τL τR V V′ = ⊤
