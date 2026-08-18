module Conversion where

-- File Charter:
--   * Intrinsically endpoint-typed reveal and conceal conversions.
--   * Structural conversion generation records the representation type in
--     each unseal/seal and computes both conversion endpoints.
--   * Store validity checks that recorded representations agree with the
--     current type store; renaming preserves intrinsic endpoints.

import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore

private
  variable
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- Replacing one abstract type by its representation
------------------------------------------------------------------------

replaceTy : TyVar Δ → Ty Δ → Ty Δ → Ty Δ
replaceTy X R (＇ Y) with X ≟ Y
replaceTy X R (＇ .X) | yes refl = R
replaceTy X R (＇ Y) | no X≠Y = ＇ Y
replaceTy X R (‵ ι) = ‵ ι
replaceTy X R ★ = ★
replaceTy X R (A ⇒ B) = replaceTy X R A ⇒ replaceTy X R B
replaceTy X R (`∀ A) = `∀ (replaceTy (Fin.suc X) (⇑ᵗ R) A)

------------------------------------------------------------------------
-- Intrinsically endpoint-typed conversion syntax
------------------------------------------------------------------------

infixr 7 _↦↑_ _↦↓_

mutual
  data Conv↑ (Δ : TyCtx) : Ty Δ → Ty Δ → Set where
    unseal : (X : TyVar Δ) (R : Ty Δ) → Conv↑ Δ (＇ X) R

    _↦↑_ : ∀ {A A′ B B′}
      → Conv↓ Δ A′ A
      → Conv↑ Δ B B′
      → Conv↑ Δ (A ⇒ B) (A′ ⇒ B′)

    `∀↑_ : ∀ {A B}
      → Conv↑ (Nat.suc Δ) A B
      → Conv↑ Δ (`∀ A) (`∀ B)

    id↑ : (A : Ty Δ) → Conv↑ Δ A A

  data Conv↓ (Δ : TyCtx) : Ty Δ → Ty Δ → Set where
    seal : (X : TyVar Δ) (R : Ty Δ) → Conv↓ Δ R (＇ X)

    _↦↓_ : ∀ {A A′ B B′}
      → Conv↑ Δ A′ A
      → Conv↓ Δ B B′
      → Conv↓ Δ (A ⇒ B) (A′ ⇒ B′)

    `∀↓_ : ∀ {A B}
      → Conv↓ (Nat.suc Δ) A B
      → Conv↓ Δ (`∀ A) (`∀ B)

    id↓ : (A : Ty Δ) → Conv↓ Δ A A

------------------------------------------------------------------------
-- Structural conversion generation
------------------------------------------------------------------------

mutual
  〖_,_↑_〗 : (X : TyVar Δ) (R B : Ty Δ)
    → Conv↑ Δ B (replaceTy X R B)
  〖 X , R ↑ (＇ Y) 〗 with X ≟ Y
  〖 X , R ↑ (＇ .X) 〗 | yes refl = unseal X R
  〖 X , R ↑ (＇ Y) 〗 | no X≠Y = id↑ (＇ Y)
  〖 X , R ↑ (‵ ι) 〗 = id↑ (‵ ι)
  〖 X , R ↑ ★ 〗 = id↑ ★
  〖 X , R ↑ (A ⇒ B) 〗 =
    makeConceal X R A ↦↑ 〖 X , R ↑ B 〗
  〖 X , R ↑ (`∀ A) 〗 = `∀↑ 〖 Fin.suc X , ⇑ᵗ R ↑ A 〗

  makeConceal : (X : TyVar Δ) (R B : Ty Δ)
    → Conv↓ Δ (replaceTy X R B) B
  makeConceal X R (＇ Y) with X ≟ Y
  makeConceal X R (＇ .X) | yes refl = seal X R
  makeConceal X R (＇ Y) | no X≠Y = id↓ (＇ Y)
  makeConceal X R (‵ ι) = id↓ (‵ ι)
  makeConceal X R ★ = id↓ ★
  makeConceal X R (A ⇒ B) =
    〖 X , R ↑ A 〗 ↦↓ makeConceal X R B
  makeConceal X R (`∀ A) =
    `∀↓ (makeConceal (Fin.suc X) (⇑ᵗ R) A)

------------------------------------------------------------------------
-- Type-variable renaming
------------------------------------------------------------------------

mutual
  rename↑ : ∀ (rho : Δ ⇒ʳ Δ′) {A B}
    → Conv↑ Δ A B
    → Conv↑ Δ′ (renameᵗ rho A) (renameᵗ rho B)
  rename↑ rho (unseal X R) = unseal (rho X) (renameᵗ rho R)
  rename↑ rho (c ↦↑ d) = rename↓ rho c ↦↑ rename↑ rho d
  rename↑ rho (`∀↑ c) = `∀↑ (rename↑ (extᵗ rho) c)
  rename↑ rho (id↑ A) = id↑ (renameᵗ rho A)

  rename↓ : ∀ (rho : Δ ⇒ʳ Δ′) {A B}
    → Conv↓ Δ A B
    → Conv↓ Δ′ (renameᵗ rho A) (renameᵗ rho B)
  rename↓ rho (seal X R) = seal (rho X) (renameᵗ rho R)
  rename↓ rho (c ↦↓ d) = rename↑ rho c ↦↓ rename↓ rho d
  rename↓ rho (`∀↓ c) = `∀↓ (rename↓ (extᵗ rho) c)
  rename↓ rho (id↓ A) = id↓ (renameᵗ rho A)

------------------------------------------------------------------------
-- Store validity
------------------------------------------------------------------------

infix 4 _⊢↑_ _⊢↓_

mutual
  data _⊢↑_ {Δ : TyCtx} (Σ : TyStore Δ) :
      ∀ {A B} → Conv↑ Δ A B → Set where
    ⊢↑-unseal : ∀ {X R}
      → Σ ∋ X ⦂ R
      → Σ ⊢↑ unseal X R

    ⊢↑-⇒ : ∀ {A A′ B B′}
        {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
      → Σ ⊢↓ c
      → Σ ⊢↑ d
      → Σ ⊢↑ c ↦↑ d

    ⊢↑-∀ : ∀ {A B} {c : Conv↑ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↑ c
      → Σ ⊢↑ `∀↑ c

    ⊢↑-id : ∀ {A}
      → Σ ⊢↑ id↑ A

  data _⊢↓_ {Δ : TyCtx} (Σ : TyStore Δ) :
      ∀ {A B} → Conv↓ Δ A B → Set where
    ⊢↓-seal : ∀ {X R}
      → Σ ∋ X ⦂ R
      → Σ ⊢↓ seal X R

    ⊢↓-⇒ : ∀ {A A′ B B′}
        {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
      → Σ ⊢↑ c
      → Σ ⊢↓ d
      → Σ ⊢↓ c ↦↓ d

    ⊢↓-∀ : ∀ {A B} {c : Conv↓ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↓ c
      → Σ ⊢↓ `∀↓ c

    ⊢↓-id : ∀ {A}
      → Σ ⊢↓ id↓ A

------------------------------------------------------------------------
-- Conversion typing indexed by an optional converted variable
------------------------------------------------------------------------

-- The pivot of a composite conversion is the join of the pivots of its
-- halves: an identity half contributes nothing, and two variable halves
-- must agree.  An all-identity conversion therefore has pivot nothing
-- and cannot be retyped at an arbitrary variable.

data PivotJoin {Δ : TyCtx} :
    Maybe (TyVar Δ) → Maybe (TyVar Δ) → Maybe (TyVar Δ) → Set where
  join-none :
      ----------------------------------
      PivotJoin nothing nothing nothing

  join-left : ∀ {X}
      ------------------------------------
    → PivotJoin (just X) nothing (just X)

  join-right : ∀ {X}
      ------------------------------------
    → PivotJoin nothing (just X) (just X)

  join-both : ∀ {X}
      -------------------------------------
    → PivotJoin (just X) (just X) (just X)

infix 4 _⊢↑[_]_ _⊢↓[_]_

mutual
  data _⊢↑[_]_ {Δ : TyCtx} (Σ : TyStore Δ) :
      Maybe (TyVar Δ) → ∀ {A B} → Conv↑ Δ A B → Set where
    ⊢↑-unsealˣ : ∀ {X R}
      → Σ ∋ X ⦂ R
        ----------------------------
      → Σ ⊢↑[ just X ] unseal X R

    ⊢↑-⇒ˣ : ∀ {p q r A A′ B B′}
        {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
      → PivotJoin p q r
      → Σ ⊢↓[ p ] c
      → Σ ⊢↑[ q ] d
        -----------------
      → Σ ⊢↑[ r ] c ↦↑ d

    ⊢↑-∀ˣ : ∀ {X A B} {c : Conv↑ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↑[ just (Fin.suc X) ] c
        -------------------------
      → Σ ⊢↑[ just X ] `∀↑ c

    ⊢↑-∀-idˣ : ∀ {A B} {c : Conv↑ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↑[ nothing ] c
        -------------------------
      → Σ ⊢↑[ nothing ] `∀↑ c

    ⊢↑-idˣ : ∀ {A}
        -----------------------
      → Σ ⊢↑[ nothing ] id↑ A

  data _⊢↓[_]_ {Δ : TyCtx} (Σ : TyStore Δ) :
      Maybe (TyVar Δ) → ∀ {A B} → Conv↓ Δ A B → Set where
    ⊢↓-sealˣ : ∀ {X R}
      → Σ ∋ X ⦂ R
        --------------------------
      → Σ ⊢↓[ just X ] seal X R

    ⊢↓-⇒ˣ : ∀ {p q r A A′ B B′}
        {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
      → PivotJoin p q r
      → Σ ⊢↑[ p ] c
      → Σ ⊢↓[ q ] d
        -----------------
      → Σ ⊢↓[ r ] c ↦↓ d

    ⊢↓-∀ˣ : ∀ {X A B} {c : Conv↓ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↓[ just (Fin.suc X) ] c
        -------------------------
      → Σ ⊢↓[ just X ] `∀↓ c

    ⊢↓-∀-idˣ : ∀ {A B} {c : Conv↓ (Nat.suc Δ) A B}
      → store-lift Σ ⊢↓[ nothing ] c
        -------------------------
      → Σ ⊢↓[ nothing ] `∀↓ c

    ⊢↓-idˣ : ∀ {A}
        -----------------------
      → Σ ⊢↓[ nothing ] id↓ A
