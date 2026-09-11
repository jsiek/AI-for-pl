{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.RuntimeAlignmentSplitProbe where

-- File Charter:
--   * Prototypes a split between inductive runtime-store provenance and
--     local source/target name alignment.
--   * Checks the concrete target alias chain produced by a `bind ★` followed
--     by a `bind (＇ zero)`, the store changes used by β-inst then β-Λ.
--   * Gives fresh, outer-premise, and inner-premise alignments over one
--     runtime world, plus small pivot witnesses between those alignments.
--   * Imports only the trusted public language definitions under GTSFImp.

import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; lookupStore)
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
import Imprecision as I

------------------------------------------------------------------------
-- Runtime provenance
------------------------------------------------------------------------

-- This layer records only how the two trusted runtime stores were built.
-- It has no center context, imprecision environment, or alignment invariant.

data RuntimeWorld : ∀ {Δᴸ Δᴿ}
    → TyStore Δᴸ
    → TyStore Δᴿ
    → Set where

  emptyʷ : RuntimeWorld store-empty store-empty

  lift-leftʷ : ∀ {Δᴸ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    → RuntimeWorld Σᴸ Σᴿ
    → RuntimeWorld (store-lift Σᴸ) Σᴿ

  lift-rightʷ : ∀ {Δᴸ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    → RuntimeWorld Σᴸ Σᴿ
    → RuntimeWorld Σᴸ (store-lift Σᴿ)

  bind-leftʷ : ∀ {Δᴸ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    → (W : RuntimeWorld Σᴸ Σᴿ)
    → (A : Ty Δᴸ)
    → RuntimeWorld (store-bind Σᴸ A) Σᴿ

  bind-rightʷ : ∀ {Δᴸ Δᴿ}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    → (W : RuntimeWorld Σᴸ Σᴿ)
    → (B : Ty Δᴿ)
    → RuntimeWorld Σᴸ (store-bind Σᴿ B)


lift-bothʷ : ∀ {Δᴸ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
  → RuntimeWorld Σᴸ Σᴿ
  → RuntimeWorld (store-lift Σᴸ) (store-lift Σᴿ)
lift-bothʷ W = lift-rightʷ (lift-leftʷ W)


bind-bothʷ : ∀ {Δᴸ Δᴿ}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
  → RuntimeWorld Σᴸ Σᴿ
  → (A : Ty Δᴸ)
  → (B : Ty Δᴿ)
  → RuntimeWorld (store-bind Σᴸ A) (store-bind Σᴿ B)
bind-bothʷ W A B = bind-rightʷ (bind-leftʷ W A) B

------------------------------------------------------------------------
-- Canonical head representations
------------------------------------------------------------------------

-- Direct lookup remains the operational notion.  These proof-only
-- functions follow a whole-variable representation through older store
-- entries, stopping at a non-variable type or a structural store lift.

resolveVar : ∀ {Δ} → TyStore Δ → TyVar Δ → Ty Δ
resolveRep : ∀ {Δ} → TyStore Δ → Ty Δ → Ty Δ

resolveVar (store-lift Σ) Fin.zero = ＇ Fin.zero
resolveVar (store-lift Σ) (Fin.suc X) = ⇑ᵗ (resolveVar Σ X)
resolveVar (store-bind Σ A) Fin.zero = ⇑ᵗ (resolveRep Σ A)
resolveVar (store-bind Σ A) (Fin.suc X) = ⇑ᵗ (resolveVar Σ X)

resolveRep Σ (＇ X) = resolveVar Σ X
resolveRep Σ (‵ ι) = ‵ ι
resolveRep Σ ★ = ★
resolveRep Σ (A ⇒ B) = A ⇒ B
resolveRep Σ (`∀ A) = `∀ A

------------------------------------------------------------------------
-- The trusted β-inst / β-Λ target-store trace
------------------------------------------------------------------------

source-store : TyStore 1
source-store = store-lift store-empty


target-store-α : TyStore 1
target-store-α = store-bind store-empty ★


target-store-βα : TyStore 2
target-store-βα = store-bind target-store-α (＇ Fin.zero)


source-X : TyVar 1
source-X = Fin.zero


target-β : TyVar 2
target-β = Fin.zero


target-α : TyVar 2
target-α = Fin.suc Fin.zero


target-β-direct : lookupStore target-store-βα target-β ≡ ＇ target-α
target-β-direct = refl


target-α-direct : lookupStore target-store-βα target-α ≡ ★
target-α-direct = refl


target-β-resolved : resolveVar target-store-βα target-β ≡ ★
target-β-resolved = refl


target-α-resolved : resolveVar target-store-βα target-α ≡ ★
target-α-resolved = refl


source-X-resolved : resolveVar source-store source-X ≡ ＇ source-X
source-X-resolved = refl


α-world : RuntimeWorld store-empty target-store-α
α-world = bind-rightʷ emptyʷ ★


βα-world : RuntimeWorld store-empty target-store-βα
βα-world = bind-rightʷ α-world (＇ Fin.zero)


final-world : RuntimeWorld source-store target-store-βα
final-world = lift-leftʷ βα-world

------------------------------------------------------------------------
-- Alignment views over one runtime world
------------------------------------------------------------------------

record Alignment {Δᴸ Δᴿ Δ}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    (W : RuntimeWorld Σᴸ Σᴿ) : Set where
  constructor alignment
  field
    ηᴸ : Δᴸ ↪ᵗ Δ
    ηᴿ : Δᴿ ↪ᵗ Δ
    marks : I.ImpEnv Δ

    resolved-representations : ∀ {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → toRenameᵗ ηᴸ Xᴸ ≡ toRenameᵗ ηᴿ Xᴿ
      → I._⊢_⊑_ marks
          (renameᵗ (toRenameᵗ ηᴸ) (resolveVar Σᴸ Xᴸ))
          (renameᵗ (toRenameᵗ ηᴿ) (resolveVar Σᴿ Xᴿ))

open Alignment public


all-dynamic : I.ImpEnv 3
all-dynamic X = I.X⊑★


-- The target identities never move between views:
--   β ↦ center 1
--   α ↦ center 2

target-η : 2 ↪ᵗ 3
target-η = skip (keep (keep empty))


-- The final alignment produced by an ordinary left lift gives X its own
-- fresh center 0.  It aligns with neither target identity.

final-source-η : 1 ↪ᵗ 3
final-source-η = keep (skip (skip empty))


final-representations : ∀ {Xᴸ : TyVar 1} {Xᴿ : TyVar 2}
  → toRenameᵗ final-source-η Xᴸ ≡ toRenameᵗ target-η Xᴿ
  → I._⊢_⊑_ all-dynamic
      (renameᵗ (toRenameᵗ final-source-η)
        (resolveVar source-store Xᴸ))
      (renameᵗ (toRenameᵗ target-η)
        (resolveVar target-store-βα Xᴿ))
final-representations {Fin.zero} {Fin.zero} ()
final-representations {Fin.zero} {Fin.suc Fin.zero} ()


final-alignment : Alignment {Δ = 3} final-world
final-alignment =
  alignment final-source-η target-η all-dynamic final-representations


-- The outer generated wrapper is viewed with X parked at α's center.

outer-source-η : 1 ↪ᵗ 3
outer-source-η = skip (skip (keep empty))


outer-representations : ∀ {Xᴸ : TyVar 1} {Xᴿ : TyVar 2}
  → toRenameᵗ outer-source-η Xᴸ ≡ toRenameᵗ target-η Xᴿ
  → I._⊢_⊑_ all-dynamic
      (renameᵗ (toRenameᵗ outer-source-η)
        (resolveVar source-store Xᴸ))
      (renameᵗ (toRenameᵗ target-η)
        (resolveVar target-store-βα Xᴿ))
outer-representations {Fin.zero} {Fin.zero} ()
outer-representations {Fin.zero} {Fin.suc Fin.zero} refl =
  I.X⊑★ refl


outer-premise-alignment : Alignment {Δ = 3} final-world
outer-premise-alignment =
  alignment outer-source-η target-η all-dynamic outer-representations


-- The inner generated wrapper is viewed with X parked at β's center.

inner-source-η : 1 ↪ᵗ 3
inner-source-η = skip (keep (skip empty))


inner-representations : ∀ {Xᴸ : TyVar 1} {Xᴿ : TyVar 2}
  → toRenameᵗ inner-source-η Xᴸ ≡ toRenameᵗ target-η Xᴿ
  → I._⊢_⊑_ all-dynamic
      (renameᵗ (toRenameᵗ inner-source-η)
        (resolveVar source-store Xᴸ))
      (renameᵗ (toRenameᵗ target-η)
        (resolveVar target-store-βα Xᴿ))
inner-representations {Fin.zero} {Fin.zero} refl = I.X⊑★ refl
inner-representations {Fin.zero} {Fin.suc Fin.zero} ()


inner-premise-alignment : Alignment {Δ = 3} final-world
inner-premise-alignment =
  alignment inner-source-η target-η all-dynamic inner-representations

------------------------------------------------------------------------
-- Local pivots change alignment, not runtime provenance
------------------------------------------------------------------------

record Pivot {Δᴸ Δᴿ Δ}
    {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
    {W : RuntimeWorld Σᴸ Σᴿ}
    (outer inner : Alignment {Δ = Δ} W)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor pivot
  field
    target-frozen : ∀ Y
      → toRenameᵗ (ηᴿ inner) Y ≡ toRenameᵗ (ηᴿ outer) Y

    marks-frozen : ∀ Z → marks inner Z ≡ marks outer Z

    pivot-aligned :
      toRenameᵗ (ηᴸ inner) Xᴸ ≡ toRenameᵗ (ηᴿ inner) Xᴿ

open Pivot public


final-to-outer-pivot :
  Pivot final-alignment outer-premise-alignment source-X target-α
final-to-outer-pivot = pivot (λ Y → refl) (λ Z → refl) refl


outer-to-inner-pivot :
  Pivot outer-premise-alignment inner-premise-alignment source-X target-β
outer-to-inner-pivot = pivot (λ Y → refl) (λ Z → refl) refl


final-to-inner-pivot :
  Pivot final-alignment inner-premise-alignment source-X target-β
final-to-inner-pivot = pivot (λ Y → refl) (λ Z → refl) refl


outer-pivot-representation :
  I._⊢_⊑_ (marks outer-premise-alignment)
    (renameᵗ (toRenameᵗ (ηᴸ outer-premise-alignment))
      (resolveVar source-store source-X))
    (renameᵗ (toRenameᵗ (ηᴿ outer-premise-alignment))
      (resolveVar target-store-βα target-α))
outer-pivot-representation =
  resolved-representations outer-premise-alignment
    {Xᴸ = source-X} {Xᴿ = target-α}
    (pivot-aligned final-to-outer-pivot)


inner-pivot-representation :
  I._⊢_⊑_ (marks inner-premise-alignment)
    (renameᵗ (toRenameᵗ (ηᴸ inner-premise-alignment))
      (resolveVar source-store source-X))
    (renameᵗ (toRenameᵗ (ηᴿ inner-premise-alignment))
      (resolveVar target-store-βα target-β))
inner-pivot-representation =
  resolved-representations inner-premise-alignment
    {Xᴸ = source-X} {Xᴿ = target-β}
    (pivot-aligned outer-to-inner-pivot)
