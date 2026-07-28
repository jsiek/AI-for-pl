module proof.Core.Properties.NarrowWidenStoreInvariantDef where

-- File Charter:
--   * Defines the store uniqueness and deterministic well-formedness
--     invariants used by narrowing and widening metatheory.
--   * Contains only the invariant definitions and their record projections.
--   * Proofs that construct or preserve these invariants live in the
--     corresponding `NarrowWidenStoreInvariantProof` module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)

open import Types
open import Store using (StoreWfAt)

StoreUnique : Store → Set
StoreUnique Σ =
  ∀ {α A B} →
  (α , A) ∈ Σ →
  (α , B) ∈ Σ →
  A ≡ B

record StoreDetWf (Δ : TyCtx) (Σ : Store) : Set₁ where
  field
    at : StoreWfAt Δ Σ
    wfOlder : ∀ {α A} → (α , A) ∈ Σ → WfTy α A
    unique : StoreUnique Σ

open StoreDetWf public
