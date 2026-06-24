module Store where

-- File Charter:
--   * Public store relations and invariants for GTSF.
--   * Defines store inclusion and store well-formedness records used in public
--     metatheory theorem statements.
--   * Proof-only store lemmas may live in `proof/` modules unless they are part
--     of this public surface.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_)
open import Data.Product using (_,_)

open import Types

------------------------------------------------------------------------
-- Store inclusion
------------------------------------------------------------------------

StoreIncl : Store → Store → Set
StoreIncl Σ Σ′ = ∀ {x} → x ∈ Σ → x ∈ Σ′

StoreIncl-refl :
  ∀ {Σ} →
  StoreIncl Σ Σ
StoreIncl-refl x∈ = x∈

StoreIncl-drop :
  ∀ {Σ α A} →
  StoreIncl Σ ((α , A) ∷ Σ)
StoreIncl-drop x∈ = there x∈

StoreIncl-cons :
  ∀ {Σ Σ′ x} →
  StoreIncl Σ Σ′ →
  StoreIncl (x ∷ Σ) (x ∷ Σ′)
StoreIncl-cons incl (here refl) = here refl
StoreIncl-cons incl (there x∈) = there (incl x∈)

------------------------------------------------------------------------
-- Store well-formedness
------------------------------------------------------------------------

record StoreWfAt (Δ : TyCtx) (Σ : Store) : Set₁ where
  field
    bound : ∀ {α A} → (α , A) ∈ Σ → α < Δ
    wfTy : ∀ {α A} → (α , A) ∈ Σ → WfTy Δ A

record StoreWf (Δ : TyCtx) (Σ : Store) : Set₁ where
  field
    at : StoreWfAt Δ Σ
    wfOlder : ∀ {α A} → (α , A) ∈ Σ → WfTy α A
    unique : ∀ {α A B} → (α , A) ∈ Σ → (α , B) ∈ Σ → A ≡ B
    len : length Σ ≡ Δ

open StoreWfAt public
open StoreWf public
