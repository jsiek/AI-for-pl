module NuStore where

-- File Charter:
--   * Nu-specific store well-formedness invariant for GTSF.
--   * Reuses the common store representation, store inclusion relation, and
--     pointwise store well-formedness from `Store.agda`.
--   * Drops the dense length invariant so Nu reduction may allocate any fresh
--     seal, not just the current store length.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)

open import Types
open import Store public
  using
    ( StoreIncl
    ; StoreIncl-refl
    ; StoreIncl-drop
    ; StoreIncl-cons
    ; StoreWfAt
    ; bound
    ; wfTy
    )

record StoreWf (Δ : TyCtx) (Σ : Store) : Set₁ where
  field
    at : StoreWfAt Δ Σ
    unique : ∀ {α A B} → (α , A) ∈ Σ → (α , B) ∈ Σ → A ≡ B

open StoreWf public
