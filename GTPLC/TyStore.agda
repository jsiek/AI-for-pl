module TyStore where

-- File Charter:
--   * Type-store representation and well-formedness invariants.
--   * Defines type-variable renaming on stores and a recursive construction
--     relation for well-formed stores.
--   * Makes type-binder lifting and fresh runtime allocation the only ways to
--     extend a well-formed store.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

open import Types

TyStore : Set
TyStore = List (TyVar × Ty)

renameTyStoreᵗ : Renameᵗ → TyStore → TyStore
renameTyStoreᵗ ρ [] = []
renameTyStoreᵗ ρ ((α , A) ∷ Σ) =
  (ρ α , renameᵗ ρ A) ∷ renameTyStoreᵗ ρ Σ

⟰ᵗ : TyStore → TyStore
⟰ᵗ = renameTyStoreᵗ suc

------------------------------------------------------------------------
-- Store well-formedness
------------------------------------------------------------------------

data StoreWf : TyCtx → TyStore → Set₁ where

  store-empty : StoreWf zero []

  store-lift : ∀ {Δ Σ Σ′}
    → StoreWf Δ Σ
    → Σ′ ≡ ⟰ᵗ Σ
      -------------------
    → StoreWf (suc Δ) Σ′

  store-bind : ∀ {Δ Σ A Σ′}
    → StoreWf Δ Σ
    → WfTy Δ A
    → Σ′ ≡ ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
      --------------------------------------
    → StoreWf (suc Δ) Σ′
