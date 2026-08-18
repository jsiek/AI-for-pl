module TyStore where

-- File Charter:
--   * Intrinsically well-scoped type stores.
--   * Makes type-binder lifting and fresh runtime allocation the only ways to
--     extend a store.
--   * Exposes direct total lookup and relates type variables to their
--     representation types in a store.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (zero; suc)
open import Data.Fin using (zero; suc)

open import Types

data TyStore : TyCtx → Set where

  store-empty : TyStore zero

  store-lift : ∀ {Δ}
    → TyStore Δ
      -------------------
    → TyStore (suc Δ)

  store-bind : ∀ {Δ}
    → TyStore Δ
    → Ty Δ
      -------------------
    → TyStore (suc Δ)

-- The direct entry for every store variable.  A structural lift represents
-- its fresh variable by that variable itself; a runtime bind exposes exactly
-- the bound type and does not follow variable indirection.

lookupStore : ∀ {Δ} → TyStore Δ → TyVar Δ → Ty Δ
lookupStore (store-lift Σ) zero = ＇ zero
lookupStore (store-lift Σ) (suc X) = ⇑ᵗ (lookupStore Σ X)
lookupStore (store-bind Σ A) zero = ⇑ᵗ A
lookupStore (store-bind Σ A) (suc X) = ⇑ᵗ (lookupStore Σ X)

infix 4 _∋_⦂_

data _∋_⦂_ : ∀ {Δ} → TyStore Δ → TyVar Δ → Ty Δ → Set where

  Z∋ : ∀ {Δ} {Σ : TyStore Δ} {A : Ty Δ} {B : Ty (suc Δ)}
    → B ≡ ⇑ᵗ A
      ----------------------------------
    → store-bind Σ A ∋ zero ⦂ B

  S-lift∋ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
      {A : Ty Δ} {B : Ty (suc Δ)}
    → Σ ∋ X ⦂ A
    → B ≡ ⇑ᵗ A
      ----------------------------------
    → store-lift Σ ∋ suc X ⦂ B

  S-bind∋ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
      {A C : Ty Δ} {B : Ty (suc Δ)}
    → Σ ∋ X ⦂ A
    → B ≡ ⇑ᵗ A
      ----------------------------------
    → store-bind Σ C ∋ suc X ⦂ B
