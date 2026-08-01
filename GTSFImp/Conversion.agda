module Conversion where

-- File Charter:
--   * Store-indexed reveal and conceal conversions for abstract type
--     representations.
--   * Reveal replaces an abstract type variable by its representation type;
--     conceal performs the inverse conversion.
--   * Conversions are raw, intrinsically scoped syntax whose typing is checked
--     against a TyStore.

import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore

private
  variable
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- Conversion syntax
------------------------------------------------------------------------

infixr 7 _↦↑_ _↦↓_

mutual
  data Conv↑ : TyCtx → Set where
    unseal : TyVar Δ → Conv↑ Δ
    _↦↑_ : Conv↓ Δ → Conv↑ Δ → Conv↑ Δ
    `∀↑_ : Conv↑ (Nat.suc Δ) → Conv↑ Δ
    id↑ : Ty Δ → Conv↑ Δ

  data Conv↓ : TyCtx → Set where
    seal : TyVar Δ → Conv↓ Δ
    _↦↓_ : Conv↑ Δ → Conv↓ Δ → Conv↓ Δ
    `∀↓_ : Conv↓ (Nat.suc Δ) → Conv↓ Δ
    id↓ : Ty Δ → Conv↓ Δ

------------------------------------------------------------------------
-- Structural conversion generation
------------------------------------------------------------------------

mutual
  〖_↑_〗 : (X : TyVar Δ) → Ty Δ → Conv↑ Δ
  〖 X ↑ (＇ Y) 〗 with X ≟ Y
  〖 X ↑ (＇ .X) 〗 | yes refl = unseal X
  〖 X ↑ (＇ Y) 〗 | no _ = id↑ (＇ Y)
  〖 X ↑ (‵ ι) 〗 = id↑ (‵ ι)
  〖 X ↑ ★ 〗 = id↑ ★
  〖 X ↑ (A ⇒ B) 〗 = makeConceal X A ↦↑ 〖 X ↑ B 〗
  〖 X ↑ (`∀ A) 〗 = `∀↑ 〖 Fin.suc X ↑ A 〗

  makeConceal : (X : TyVar Δ) → Ty Δ → Conv↓ Δ
  makeConceal X (＇ Y) with X ≟ Y
  makeConceal X (＇ .X) | yes refl = seal X
  makeConceal X (＇ Y) | no _ = id↓ (＇ Y)
  makeConceal X (‵ ι) = id↓ (‵ ι)
  makeConceal X ★ = id↓ ★
  makeConceal X (A ⇒ B) = 〖 X ↑ A 〗 ↦↓ makeConceal X B
  makeConceal X (`∀ A) = `∀↓ (makeConceal (Fin.suc X) A)

------------------------------------------------------------------------
-- Type-variable renaming
------------------------------------------------------------------------

mutual
  rename↑ : Δ ⇒ʳ Δ′ → Conv↑ Δ → Conv↑ Δ′
  rename↑ ρ (unseal X) = unseal (ρ X)
  rename↑ ρ (c ↦↑ d) = rename↓ ρ c ↦↑ rename↑ ρ d
  rename↑ ρ (`∀↑ c) = `∀↑ (rename↑ (extᵗ ρ) c)
  rename↑ ρ (id↑ A) = id↑ (renameᵗ ρ A)

  rename↓ : Δ ⇒ʳ Δ′ → Conv↓ Δ → Conv↓ Δ′
  rename↓ ρ (seal X) = seal (ρ X)
  rename↓ ρ (c ↦↓ d) = rename↑ ρ c ↦↓ rename↓ ρ d
  rename↓ ρ (`∀↓ c) = `∀↓ (rename↓ (extᵗ ρ) c)
  rename↓ ρ (id↓ A) = id↓ (renameᵗ ρ A)

------------------------------------------------------------------------
-- Store-indexed conversion typing
------------------------------------------------------------------------

infix 4 _⊢_⦂_↑ˢ_ _⊢_⦂_↓ˢ_

mutual
  data _⊢_⦂_↑ˢ_ {Δ : TyCtx} (Σ : TyStore Δ) :
      Conv↑ Δ → Ty Δ → Ty Δ → Set where

    ⊢↑-unseal : ∀ {X A}
      → Σ ∋ X ⦂ A
        ----------------------------
      → Σ ⊢ unseal X ⦂ ＇ X ↑ˢ A

    ⊢↑-⇒ : ∀ {A A′ B B′ c d}
      → Σ ⊢ c ⦂ A′ ↓ˢ A
      → Σ ⊢ d ⦂ B ↑ˢ B′
        -------------------------------------------
      → Σ ⊢ c ↦↑ d ⦂ (A ⇒ B) ↑ˢ (A′ ⇒ B′)

    ⊢↑-∀ : ∀ {A B c}
      → store-lift Σ ⊢ c ⦂ A ↑ˢ B
        --------------------------------
      → Σ ⊢ `∀↑ c ⦂ (`∀ A) ↑ˢ (`∀ B)

    ⊢↑-id : ∀ {A}
        --------------------
      → Σ ⊢ id↑ A ⦂ A ↑ˢ A

  data _⊢_⦂_↓ˢ_ {Δ : TyCtx} (Σ : TyStore Δ) :
      Conv↓ Δ → Ty Δ → Ty Δ → Set where

    ⊢↓-seal : ∀ {X A}
      → Σ ∋ X ⦂ A
        --------------------------
      → Σ ⊢ seal X ⦂ A ↓ˢ ＇ X

    ⊢↓-⇒ : ∀ {A A′ B B′ c d}
      → Σ ⊢ c ⦂ A′ ↑ˢ A
      → Σ ⊢ d ⦂ B ↓ˢ B′
        -------------------------------------------
      → Σ ⊢ c ↦↓ d ⦂ (A ⇒ B) ↓ˢ (A′ ⇒ B′)

    ⊢↓-∀ : ∀ {A B c}
      → store-lift Σ ⊢ c ⦂ A ↓ˢ B
        --------------------------------
      → Σ ⊢ `∀↓ c ⦂ (`∀ A) ↓ˢ (`∀ B)

    ⊢↓-id : ∀ {A}
        --------------------
      → Σ ⊢ id↓ A ⦂ A ↓ˢ A
