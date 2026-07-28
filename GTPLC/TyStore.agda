module TyStore where

-- File Charter:
--   * Type-store representation and well-formedness invariants.
--   * Defines type-variable renaming on stores and the invariants assumed by
--     preservation.

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

record StoreWf (Δ : TyCtx) (Σ : TyStore) : Set₁ where
  field
    bound : ∀ {α A} → (α , A) ∈ Σ → α < Δ
    wfTy : ∀ {α A} → (α , A) ∈ Σ → WfTy Δ A
    unique : ∀ {α A B} → (α , A) ∈ Σ → (α , B) ∈ Σ → A ≡ B

open StoreWf public
