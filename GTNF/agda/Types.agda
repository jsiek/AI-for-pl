module Types where

-- File Charter:
--   * (GTNF) FORKED FROM strong-rep-nu.Types, with the dynamic type `★`
--     (design.md §1) and the decidable equality `_≟ᵗ_` the tag rules
--     compare with.
--   * THE TYPE SYNTAX AND ITS SUBSTITUTION OPERATIONS.  `TyVar` (= ℕ)
--     and `Ty` (`` `_ ``, `` `ℕ ``, `` `𝔹 ``, `_⇒_`, `` `∀ ``);
--     parallel renaming and substitution `renameᵗ`/`substᵗ` with
--     `extᵗ`/`extsᵗ`/`⇑ᵗ`; single substitution `_[_]ᵗ` (via
--     `singleTyEnv`), `idᵗ` and `_•ᵗ_`; and the index-directed
--     substitution `single-at`/`_[_:=_]ᵗ`.
--     Mirrors SystemF/agda/extrinsic/Types.agda.
--   * NO LEMMAS.  The equational facts about these operations live in
--     proof.Types (`substᵗ-cong`, `extsᵗ-renᵗ`, `substᵗ-renᵗ`);
--     the full algebraic theory — composition `_⨟ᵗ_`, `sub-sub`,
--     `substitution`, `exts-sub-cons` — is proof.TypeSubst. 
-- Nothing
--     here knows about the binder/seal discipline or the two de Bruijn
--     universes: that is Ctx.
--   * ONE SYNTAX, TWO READINGS.  A `Ty` carries no universe tag.  The
--     same term is read either as an ORDINARY type or as a
--     REPRESENTATION payload, and it is Ctx §5 (`_⊢_~_`,
--     `_⊢_≈_⊣_`) that relates the two readings — never
--     anything in this file (notes/DECISIONS.md, 2026-09-20, the
--     context-layer split by subject).  The consequence for §4:
--     `single-at` leaves every index but X alone, because a CONCEALED
--     ordinary variable stays in the context, while `singleTyEnv`
--     shifts the rest down because reveal/tapp ELIMINATE their
--     variable.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Type variables and types
------------------------------------------------------------------------

TyVar : Set
TyVar = ℕ

infixr 7 _⇒_
infix 6 `∀

data Ty : Set where
  `_  : TyVar → Ty        -- X
  `ℕ  : Ty                -- ℕ
  `𝔹  : Ty                -- 𝔹
  ★   : Ty                -- ★, the dynamic type (GTNF, new)
  _⇒_ : Ty → Ty → Ty      -- A → B
  `∀  : Ty → Ty           -- ∀X.A   (A is a type with one more type variable)

-- The base types: the types of the literals, and where a bare `id` and
-- the `Id` rule sit.
data Base : Ty → Set where
  base-ℕ : Base `ℕ
  base-𝔹 : Base `𝔹

------------------------------------------------------------------------
-- Parallel renaming and substitution on types
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = TyVar → TyVar

Substᵗ : Set
Substᵗ = TyVar → Ty

renᵗ : Renameᵗ → Substᵗ
renᵗ ρ X = ` (ρ X)

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ zero    = zero
extᵗ ρ (suc X) = suc (ρ X)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (` X)   = ` (ρ X)
renameᵗ ρ `ℕ      = `ℕ
renameᵗ ρ `𝔹      = `𝔹
renameᵗ ρ ★       = ★
renameᵗ ρ (A ⇒ B) = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A)  = `∀ (renameᵗ (extᵗ ρ) A)

⇑ᵗ : Ty → Ty
⇑ᵗ = renameᵗ suc

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ zero    = ` zero
extsᵗ σ (suc X) = ⇑ᵗ (σ X)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (` X)   = σ X
substᵗ σ `ℕ      = `ℕ
substᵗ σ `𝔹      = `𝔹
substᵗ σ ★       = ★
substᵗ σ (A ⇒ B) = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A)  = `∀ (substᵗ (extsᵗ σ) A)

------------------------------------------------------------------------
-- Single substitution and cons
------------------------------------------------------------------------

singleTyEnv : Ty → Substᵗ
singleTyEnv B zero    = B
singleTyEnv B (suc X) = ` X

-- A [ B ]ᵗ : replace the outermost type variable of A by B  (the type-level
-- action of X:=B, i.e. substᵗ (singleTyEnv B) A).
infix 8 _[_]ᵗ
_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

idᵗ : Substᵗ
idᵗ = `_

infixr 6 _•ᵗ_
_•ᵗ_ : Ty → Substᵗ → Substᵗ
(A •ᵗ σ) zero    = A
(A •ᵗ σ) (suc X) = σ X

------------------------------------------------------------------------
-- Substitution at a specific index (the (conceal) substitution)
------------------------------------------------------------------------

-- single-at X A : replace the type variable at index X by A, leaving every
-- other index UNCHANGED — no shift-down, because the concealed variable stays
-- in the context.  Contrast singleTyEnv, which substitutes index 0 and shifts
-- the rest down (used by reveal/tapp, which eliminate their variable).
single-at : ℕ → Ty → Substᵗ
single-at X A Y with X ≟ Y
single-at X A Y | yes _ = A
single-at X A Y | no  _ = ` Y

-- B [ X := A ]ᵗ : substitute A for the general index X in B.  Its
-- substitution `single-at` is what proof.Preserve reasons about
-- (`single-at-hit`, `single-at-miss`, `single-at-ext`).
infix 8 _[_:=_]ᵗ
_[_:=_]ᵗ : Ty → ℕ → Ty → Ty
B [ X := A ]ᵗ = substᵗ (single-at X A) B

------------------------------------------------------------------------
-- Decidable equality (GTNF: `TagUntag`/`TagUntagBad` compare tags)
------------------------------------------------------------------------

infix 4 _≟ᵗ_
_≟ᵗ_ : (A B : Ty) → Dec (A ≡ B)
(` X) ≟ᵗ (` Y) with X ≟ Y
(` X) ≟ᵗ (` Y) | yes refl = yes refl
(` X) ≟ᵗ (` Y) | no ne = no (λ { refl → ne refl })
(` X) ≟ᵗ `ℕ = no (λ ())
(` X) ≟ᵗ `𝔹 = no (λ ())
(` X) ≟ᵗ ★ = no (λ ())
(` X) ≟ᵗ (C ⇒ D) = no (λ ())
(` X) ≟ᵗ (`∀ C) = no (λ ())
`ℕ ≟ᵗ (` Y) = no (λ ())
`ℕ ≟ᵗ `ℕ = yes refl
`ℕ ≟ᵗ `𝔹 = no (λ ())
`ℕ ≟ᵗ ★ = no (λ ())
`ℕ ≟ᵗ (C ⇒ D) = no (λ ())
`ℕ ≟ᵗ (`∀ C) = no (λ ())
`𝔹 ≟ᵗ (` Y) = no (λ ())
`𝔹 ≟ᵗ `ℕ = no (λ ())
`𝔹 ≟ᵗ `𝔹 = yes refl
`𝔹 ≟ᵗ ★ = no (λ ())
`𝔹 ≟ᵗ (C ⇒ D) = no (λ ())
`𝔹 ≟ᵗ (`∀ C) = no (λ ())
★ ≟ᵗ (` Y) = no (λ ())
★ ≟ᵗ `ℕ = no (λ ())
★ ≟ᵗ `𝔹 = no (λ ())
★ ≟ᵗ ★ = yes refl
★ ≟ᵗ (C ⇒ D) = no (λ ())
★ ≟ᵗ (`∀ C) = no (λ ())
(A ⇒ B) ≟ᵗ (` Y) = no (λ ())
(A ⇒ B) ≟ᵗ `ℕ = no (λ ())
(A ⇒ B) ≟ᵗ `𝔹 = no (λ ())
(A ⇒ B) ≟ᵗ ★ = no (λ ())
(A ⇒ B) ≟ᵗ (C ⇒ D) with A ≟ᵗ C | B ≟ᵗ D
(A ⇒ B) ≟ᵗ (C ⇒ D) | yes refl | yes refl = yes refl
(A ⇒ B) ≟ᵗ (C ⇒ D) | yes refl | no ne = no (λ { refl → ne refl })
(A ⇒ B) ≟ᵗ (C ⇒ D) | no ne | e = no (λ { refl → ne refl })
(A ⇒ B) ≟ᵗ (`∀ C) = no (λ ())
(`∀ A) ≟ᵗ (` Y) = no (λ ())
(`∀ A) ≟ᵗ `ℕ = no (λ ())
(`∀ A) ≟ᵗ `𝔹 = no (λ ())
(`∀ A) ≟ᵗ ★ = no (λ ())
(`∀ A) ≟ᵗ (C ⇒ D) = no (λ ())
(`∀ A) ≟ᵗ (`∀ C) with A ≟ᵗ C
(`∀ A) ≟ᵗ (`∀ C) | yes refl = yes refl
(`∀ A) ≟ᵗ (`∀ C) | no ne = no (λ { refl → ne refl })
