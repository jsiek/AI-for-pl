module Conversion where

-- File Charter:
--   * Intrinsically endpoint-typed reveal and conceal conversions.
--   * Structural conversion generation records the representation type in
--     each unseal/seal and computes both conversion endpoints.
--   * Generator-indexed validity tracks the one store variable and direct
--     representation from which a structural conversion was generated.
--   * Renaming preserves intrinsic endpoints.

import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
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
-- Generator-indexed store validity
------------------------------------------------------------------------

-- A valid conversion has one generator `X` with direct representation `R`.
-- Its syntax is exactly the structural conversion generated at `X`: arrows
-- use the same generator in both halves, and universals shift that generator
-- beneath the binder.  Identity leaves are permitted only where the generator
-- cannot occur.  The explicit equality in each universal rule keeps the
-- representation index in constructor form.

infix 4 _⊢↑[_⦂_]_ _⊢↓[_⦂_]_

mutual
  data _⊢↑[_⦂_]_ {Δ : TyCtx} (Σ : TyStore Δ)
      (X : TyVar Δ) (R : Ty Δ) :
      ∀ {A B} → Conv↑ Δ A B → Set where
    ⊢↑-unseal :
        Σ ∋ X ⦂ R
        ----------------------------
      → Σ ⊢↑[ X ⦂ R ] unseal X R

    ⊢↑-⇒ : ∀ {A A′ B B′}
        {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
      → Σ ⊢↓[ X ⦂ R ] c
      → Σ ⊢↑[ X ⦂ R ] d
        -------------------------
      → Σ ⊢↑[ X ⦂ R ] c ↦↑ d

    ⊢↑-∀ : ∀ {R′ A B} {c : Conv↑ (Nat.suc Δ) A B}
      → R′ ≡ ⇑ᵗ R
      → store-lift Σ ⊢↑[ Fin.suc X ⦂ R′ ] c
        -------------------------
      → Σ ⊢↑[ X ⦂ R ] `∀↑ c

    ⊢↑-id-var : ∀ {Y}
      → Σ ∋ X ⦂ R
      → X ≢ Y
        ---------------------------
      → Σ ⊢↑[ X ⦂ R ] id↑ (＇ Y)

    ⊢↑-id-base : ∀ {ι}
      → Σ ∋ X ⦂ R
        ---------------------------
      → Σ ⊢↑[ X ⦂ R ] id↑ (‵ ι)

    ⊢↑-id-star :
        Σ ∋ X ⦂ R
        -------------------------
      → Σ ⊢↑[ X ⦂ R ] id↑ ★

  data _⊢↓[_⦂_]_ {Δ : TyCtx} (Σ : TyStore Δ)
      (X : TyVar Δ) (R : Ty Δ) :
      ∀ {A B} → Conv↓ Δ A B → Set where
    ⊢↓-seal :
        Σ ∋ X ⦂ R
        --------------------------
      → Σ ⊢↓[ X ⦂ R ] seal X R

    ⊢↓-⇒ : ∀ {A A′ B B′}
        {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
      → Σ ⊢↑[ X ⦂ R ] c
      → Σ ⊢↓[ X ⦂ R ] d
        -------------------------
      → Σ ⊢↓[ X ⦂ R ] c ↦↓ d

    ⊢↓-∀ : ∀ {R′ A B} {c : Conv↓ (Nat.suc Δ) A B}
      → R′ ≡ ⇑ᵗ R
      → store-lift Σ ⊢↓[ Fin.suc X ⦂ R′ ] c
        -------------------------
      → Σ ⊢↓[ X ⦂ R ] `∀↓ c

    ⊢↓-id-var : ∀ {Y}
      → Σ ∋ X ⦂ R
      → X ≢ Y
        ---------------------------
      → Σ ⊢↓[ X ⦂ R ] id↓ (＇ Y)

    ⊢↓-id-base : ∀ {ι}
      → Σ ∋ X ⦂ R
        ---------------------------
      → Σ ⊢↓[ X ⦂ R ] id↓ (‵ ι)

    ⊢↓-id-star :
        Σ ∋ X ⦂ R
        -------------------------
      → Σ ⊢↓[ X ⦂ R ] id↓ ★
