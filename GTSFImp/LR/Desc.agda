module LR.Desc where

-- File Charter:
--   * Descriptors: syntactic closures that name relations between left
--     and right runtime values (notes/logrel-dgg.md, Section 6.11).
--     A descriptor is a two-context precision derivation together with
--     an environment for its variables, over the two runtime stores.
--   * An entry describes a variable's values: the left values are
--     sealed by a nonempty list of left store variables (outermost
--     first), the right values by a list of right store variables, and
--     the contents are related by a descriptor.
--       - shared variable:      seals Xl [] [ Xr ] c
--       - left-only variable:   seals Xl [] [] c
--       - after a right `inst` (notes/denotational-dgg.md, 8b):
--                               seals σ [] [ β′ , α′ ] c
--   * A tag describes how a left value tagged with a left store
--     variable relates to a right `★` value: the right tag variable, if
--     the right tags too, and an entry for the payloads.
--   * Descriptors are syntax, so the relations can quantify over them
--     without leaving `Set`.  Quantifying over semantic relations, as
--     PolyGν does on paper, needs an impredicative universe.
--   * Renaming along order-preserving embeddings of the stores.

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Types
open import Consistency using (_↪ᵗ_; toRenameᵗ)
open import LR.Precision

------------------------------------------------------------------------
-- Descriptors and entries
------------------------------------------------------------------------

mutual
  data Desc (ΔL ΔR : TyCtx) : Set where
    desc : ∀ {Δ Δ′} {Φ : Corr Δ Δ′} {A A′}
      → Φ ⊢ A ⊑ A′
      → (TyVar Δ → Entry ΔL ΔR)
      → (Δ′ ⇒ˢ ΔR)
      → Desc ΔL ΔR

  data Entry (ΔL ΔR : TyCtx) : Set where
    seals : TyVar ΔL → List (TyVar ΔL) → List (TyVar ΔR)
      → Desc ΔL ΔR → Entry ΔL ΔR

-- how a left value tagged with a store variable relates to a right
-- `★` value
Tag : TyCtx → TyCtx → Set
Tag ΔL ΔR = Maybe (TyVar ΔR) × Entry ΔL ΔR

------------------------------------------------------------------------
-- The types a descriptor relates
------------------------------------------------------------------------

-- the left type of a variable: its outermost seal
entryTy : ∀ {ΔL ΔR} → Entry ΔL ΔR → Ty ΔL
entryTy (seals X Xs Ys c) = ＇ X

leftTy : ∀ {ΔL ΔR} → Desc ΔL ΔR → Ty ΔL
leftTy (desc {A = A} p env envR) = substᵗ (λ X → entryTy (env X)) A

rightTy : ∀ {ΔL ΔR} → Desc ΔL ΔR → Ty ΔR
rightTy (desc {A′ = A′} p env envR) = substᵗ envR A′

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

renameVar : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → TyVar Δ → TyVar Δ′
renameVar σ = toRenameᵗ σ

mutual
  renameDesc : ∀ {ΔL ΔL′ ΔR ΔR′}
    → ΔL ↪ᵗ ΔL′ → ΔR ↪ᵗ ΔR′ → Desc ΔL ΔR → Desc ΔL′ ΔR′
  renameDesc σL σR (desc p env envR) =
    desc p (λ X → renameEntry σL σR (env X))
      (λ Y → renameᵗ (toRenameᵗ σR) (envR Y))

  renameEntry : ∀ {ΔL ΔL′ ΔR ΔR′}
    → ΔL ↪ᵗ ΔL′ → ΔR ↪ᵗ ΔR′ → Entry ΔL ΔR → Entry ΔL′ ΔR′
  renameEntry σL σR (seals X Xs Ys c) =
    seals (renameVar σL X) (map (renameVar σL) Xs) (map (renameVar σR) Ys)
      (renameDesc σL σR c)

renameTag : ∀ {ΔL ΔL′ ΔR ΔR′}
  → ΔL ↪ᵗ ΔL′ → ΔR ↪ᵗ ΔR′ → Tag ΔL ΔR → Tag ΔL′ ΔR′
renameTag σL σR (just Y , e) = just (renameVar σR Y) , renameEntry σL σR e
renameTag σL σR (nothing , e) = nothing , renameEntry σL σR e
