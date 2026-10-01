module Imprecision where

-- File Charter:
--   * TYPE IMPRECISION, COPIED FROM GTSFImp/Imprecision.agda (design.md
--     §12.1): the same fifteen-odd rules, the same `VarImp` marks
--     (`X⊑X`, `X⊑★`), the same `idᵐ`/`extᵐ`/`instᵐ`, and the same
--     structural `∀⊑`, `∀★⊑★`, `∀⊑★`, `bot-elim`, `bot⊑★` clauses.
--   * TWO DE BRUIJN READINGS OF GTSFImp's INTRINSIC FILE.  (1) GTNF's
--     `Ty` is extrinsic, so an imprecision environment is a LIST
--     parallel to `names Δ` (head = index 0), as `ModeEnv` is in
--     Coercion; `X⊑★`'s premise is a list lookup.  (2) GTSFImp's
--     `‵ ι` is GTNF's two base types, read through `Base`.
--   * NOT THE CONSISTENCY MODES.  `VarImp` relates two programs;
--     Coercion's `Mode` types the casts within one program
--     (design.md §9.4).  The two lattices are never mixed.
--   * DEFINITIONS ONLY: `refl⊑`, `⊑-trans`, `⊑-unique` are to be
--     ported from GTSFImp's proof/ tree when the DGG needs them.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)

open import Types
open import Ctx using (_∋ˡ_:=_)
open import Coercion using (NonVar; NonStar; _∈ᵗ_)

------------------------------------------------------------------------
-- Marks and environments (GTSFImp `VarImp`, `ImpEnv`)
------------------------------------------------------------------------

data VarImp : Set where
  X⊑X : VarImp
  X⊑★ : VarImp

-- One mark per ordinary name, parallel to `names Δ` (head = index 0).
ImpEnv : Set
ImpEnv = List VarImp

-- every name in scope at `X⊑X`: GTSFImp's `idᵐ` at the length of Δ
idᵐ : ∀ {A : Set} → List A → ImpEnv
idᵐ = map (λ _ → X⊑X)

extᵐ : ImpEnv → ImpEnv
extᵐ μ = X⊑X ∷ μ

instᵐ : ImpEnv → ImpEnv
instᵐ μ = X⊑★ ∷ μ

------------------------------------------------------------------------
-- Imprecision  μ ⊢ A ⊑ B   (A the more precise type)
------------------------------------------------------------------------

private
  variable
    μ : ImpEnv
    A A′ B B′ ι : Ty
    X : ℕ

infix 4 _⊢_⊑_

data _⊢_⊑_ (μ : ImpEnv) : Ty → Ty → Set where

  ★⊑★ :
      -------------
      μ ⊢ ★ ⊑ ★

  ι⊑ι : Base ι
      ---------------
    → μ ⊢ ι ⊑ ι

  X⊑X : ∀ {X}
      -------------------
    → μ ⊢ ` X ⊑ ` X

  ⇒⊑⇒ : μ ⊢ A ⊑ A′
    → μ ⊢ B ⊑ B′
      ---------------------------
    → μ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ∀⊑∀ : extᵐ μ ⊢ A ⊑ B
      -----------------------
    → μ ⊢ (`∀ A) ⊑ (`∀ B)

  ⇒⊑★ : μ ⊢ A ⊑ ★
    → μ ⊢ B ⊑ ★
      -----------------
    → μ ⊢ A ⇒ B ⊑ ★

  ι⊑★ : Base ι
      ---------------
    → μ ⊢ ι ⊑ ★

  X⊑★ : μ ∋ˡ X := X⊑★
      ----------------
    → μ ⊢ ` X ⊑ ★

  ∀⊑ : NonVar A
    → 0 ∈ᵗ A
    → instᵐ μ ⊢ A ⊑ ⇑ᵗ B
      ---------------------------
    → μ ⊢ (`∀ A) ⊑ B

  ∀★⊑★ :
      ------------------
    μ ⊢ (`∀ ★) ⊑ ★

  ∀⊑★ : NonStar A
    → extᵐ μ ⊢ A ⊑ ★
      -----------------
    → μ ⊢ (`∀ A) ⊑ ★

  bot-elim :
      --------------------------------
    μ ⊢ (`∀ (` 0)) ⊑ (`∀ ★)

  bot⊑★ :
      ---------------------------
    μ ⊢ (`∀ (` 0)) ⊑ ★
