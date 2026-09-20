module strong.Types where

-- Strong System F — types and type-variable substitution.
--
-- Types are ordinary System F types in de Bruijn form; a type variable is a
-- natural-number index (` X).  Renaming and (parallel) substitution are the
-- standard operations, mirroring SystemF/agda/extrinsic/Types.agda.  Nothing
-- here knows about the binder/seal discipline — that lives in strong.Ctx.
-- The lemmas about these operations live in strong.proof.Types.

open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)

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
  _⇒_ : Ty → Ty → Ty      -- A → B
  `∀  : Ty → Ty           -- ∀X.A   (A is a type with one more type variable)

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
... | yes _ = A
... | no  _ = ` Y

-- B [ X := A ]ᵗ : substitute A for the general index X in B  (used by (conceal)).
infix 8 _[_:=_]ᵗ
_[_:=_]ᵗ : Ty → ℕ → Ty → Ty
B [ X := A ]ᵗ = substᵗ (single-at X A) B

-- downTyEnv X A : move a type from the ambient context Δ INTO the prefix Δ ↓ X
-- (which drops indices 0..X).  The concealed variable X becomes its
-- representation A; deeper variables Y > X shift down by X+1 to fill the dropped
-- slots.  (Used by TyWrapCncl to reindex a type argument into the conceal body's
-- prefix, where X is no longer visible and is replaced by its rep.)
downTyEnv : ℕ → Ty → Substᵗ
downTyEnv X A Y with X ≟ Y
... | yes _ = A
... | no  _ = ` (Y ∸ suc X)
