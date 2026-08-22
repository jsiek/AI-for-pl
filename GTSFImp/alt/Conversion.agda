module alt.Conversion where

-- File Charter:
--   * Defines intrinsically endpoint-typed shift-free conversions.
--   * Identity leaves are restricted to atoms.
--   * Pivot strictness states that every seal or unseal leaf uses one
--     supplied scoped variable; an all-identity delimiter is permitted.

import Data.Fin as Fin
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Types

private
  variable
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- Inserting one scoped-variable slot
------------------------------------------------------------------------

punchIn : ∀ {Δ} → Fin (Nat.suc Δ) → Fin Δ → Fin (Nat.suc Δ)
punchIn zero Y = suc Y
punchIn (suc X) zero = zero
punchIn (suc X) (suc Y) = suc (punchIn X Y)

wkᵗ : ∀ {Δ} → Fin (Nat.suc Δ) → Ty Δ → Ty (Nat.suc Δ)
wkᵗ X = renameᵗ (punchIn X)

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
replaceTy X R (`∀ A) = `∀ (replaceTy (suc X) (⇑ᵗ R) A)

------------------------------------------------------------------------
-- Intrinsically endpoint-typed conversions
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

    id↑ : ∀ {A}
      → Atom A
      → Conv↑ Δ A A

  data Conv↓ (Δ : TyCtx) : Ty Δ → Ty Δ → Set where
    seal : (X : TyVar Δ) (R : Ty Δ) → Conv↓ Δ R (＇ X)

    _↦↓_ : ∀ {A A′ B B′}
      → Conv↑ Δ A′ A
      → Conv↓ Δ B B′
      → Conv↓ Δ (A ⇒ B) (A′ ⇒ B′)

    `∀↓_ : ∀ {A B}
      → Conv↓ (Nat.suc Δ) A B
      → Conv↓ Δ (`∀ A) (`∀ B)

    id↓ : ∀ {A}
      → Atom A
      → Conv↓ Δ A A

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
  〖 X , R ↑ (`∀ A) 〗 = `∀↑ 〖 suc X , ⇑ᵗ R ↑ A 〗

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
    `∀↓ (makeConceal (suc X) (⇑ᵗ R) A)

------------------------------------------------------------------------
-- Structural delimiters
------------------------------------------------------------------------

mutual
  delimiter↑ : (A : Ty Δ) → Conv↑ Δ A A
  delimiter↑ (＇ X) = id↑ (＇ X)
  delimiter↑ (‵ ι) = id↑ (‵ ι)
  delimiter↑ ★ = id↑ ★
  delimiter↑ (A ⇒ B) = delimiter↓ A ↦↑ delimiter↑ B
  delimiter↑ (`∀ A) = `∀↑ delimiter↑ A

  delimiter↓ : (A : Ty Δ) → Conv↓ Δ A A
  delimiter↓ (＇ X) = id↓ (＇ X)
  delimiter↓ (‵ ι) = id↓ (‵ ι)
  delimiter↓ ★ = id↓ ★
  delimiter↓ (A ⇒ B) = delimiter↑ A ↦↓ delimiter↓ B
  delimiter↓ (`∀ A) = `∀↓ delimiter↓ A

------------------------------------------------------------------------
-- Type-variable renaming
------------------------------------------------------------------------

mutual
  rename↑ : ∀ (ρ : Δ ⇒ʳ Δ′) {A B}
    → Conv↑ Δ A B
    → Conv↑ Δ′ (renameᵗ ρ A) (renameᵗ ρ B)
  rename↑ ρ (unseal X R) = unseal (ρ X) (renameᵗ ρ R)
  rename↑ ρ (c ↦↑ d) = rename↓ ρ c ↦↑ rename↑ ρ d
  rename↑ ρ (`∀↑ c) = `∀↑ (rename↑ (extᵗ ρ) c)
  rename↑ ρ (id↑ a) = id↑ (renameAtom ρ a)

  rename↓ : ∀ (ρ : Δ ⇒ʳ Δ′) {A B}
    → Conv↓ Δ A B
    → Conv↓ Δ′ (renameᵗ ρ A) (renameᵗ ρ B)
  rename↓ ρ (seal X R) = seal (ρ X) (renameᵗ ρ R)
  rename↓ ρ (c ↦↓ d) = rename↑ ρ c ↦↓ rename↓ ρ d
  rename↓ ρ (`∀↓ c) = `∀↓ (rename↓ (extᵗ ρ) c)
  rename↓ ρ (id↓ a) = id↓ (renameAtom ρ a)

  renameAtom : ∀ (ρ : Δ ⇒ʳ Δ′) {A}
    → Atom A
    → Atom (renameᵗ ρ A)
  renameAtom ρ (＇ X) = ＇ (ρ X)
  renameAtom ρ (‵ ι) = ‵ ι
  renameAtom ρ ★ = ★

------------------------------------------------------------------------
-- Pivot strictness
------------------------------------------------------------------------

mutual
  data PivotStrict↑ {Δ : TyCtx} (X : TyVar Δ) :
      ∀ {A B} → Conv↑ Δ A B → Set where
    strict-unseal : ∀ {R}
      → PivotStrict↑ X (unseal X R)

    strict-↑⇒ : ∀ {A A′ B B′}
        {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
      → PivotStrict↓ X c
      → PivotStrict↑ X d
      → PivotStrict↑ X (c ↦↑ d)

    strict-↑∀ : ∀ {A B} {c : Conv↑ (Nat.suc Δ) A B}
      → PivotStrict↑ (suc X) c
      → PivotStrict↑ X (`∀↑ c)

    strict-id↑ : ∀ {A} {a : Atom A}
      → PivotStrict↑ X (id↑ a)

  data PivotStrict↓ {Δ : TyCtx} (X : TyVar Δ) :
      ∀ {A B} → Conv↓ Δ A B → Set where
    strict-seal : ∀ {R}
      → PivotStrict↓ X (seal X R)

    strict-↓⇒ : ∀ {A A′ B B′}
        {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
      → PivotStrict↑ X c
      → PivotStrict↓ X d
      → PivotStrict↓ X (c ↦↓ d)

    strict-↓∀ : ∀ {A B} {c : Conv↓ (Nat.suc Δ) A B}
      → PivotStrict↓ (suc X) c
      → PivotStrict↓ X (`∀↓ c)

    strict-id↓ : ∀ {A} {a : Atom A}
      → PivotStrict↓ X (id↓ a)

mutual
  delimiter-strict↑ : ∀ {Δ} (X : TyVar Δ) (A : Ty Δ)
    → PivotStrict↑ X (delimiter↑ A)
  delimiter-strict↑ X (＇ Y) = strict-id↑
  delimiter-strict↑ X (‵ ι) = strict-id↑
  delimiter-strict↑ X ★ = strict-id↑
  delimiter-strict↑ X (A ⇒ B) =
    strict-↑⇒ (delimiter-strict↓ X A) (delimiter-strict↑ X B)
  delimiter-strict↑ X (`∀ A) = strict-↑∀ (delimiter-strict↑ (suc X) A)

  delimiter-strict↓ : ∀ {Δ} (X : TyVar Δ) (A : Ty Δ)
    → PivotStrict↓ X (delimiter↓ A)
  delimiter-strict↓ X (＇ Y) = strict-id↓
  delimiter-strict↓ X (‵ ι) = strict-id↓
  delimiter-strict↓ X ★ = strict-id↓
  delimiter-strict↓ X (A ⇒ B) =
    strict-↓⇒ (delimiter-strict↑ X A) (delimiter-strict↓ X B)
  delimiter-strict↓ X (`∀ A) = strict-↓∀ (delimiter-strict↓ (suc X) A)
