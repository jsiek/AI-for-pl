module Terms where

-- File Charter:
--   * Canonical syntax, values, runtime invariants, variable actions, and
--     typing for Nu GTSF terms.
--   * `Scopedᵐ` records the term-variable scope of raw syntax; `Closedᵐ` is
--     its closed-term specialization.
--   * Algebraic and typing properties belong in
--     `proof.Core.Properties.NuTermProperties`.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

open import Types
open import TyStore
open import Ctx
open import Coercions
open import Primitives

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_
infix  5 Λ_
infix  5 ν_·_•⟨_⟩
infixl 7 _·_
infixl 7 _⟨_⟩
infixl 6 _⊕[_]_
infix  9 `_

Var : Set
Var = ℕ

data Term : Set where
  `_      : Var → Term
  ƛ_      : Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  ν_·_•⟨_⟩ : Ty → Term → Coercion → Term
  $       : Const → Term
  _⊕[_]_  : Term → Prim → Term → Term
  _⟨_⟩    : Term → Coercion → Term
  blame   : Term

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : Term → Set where
  ƛ_ : (N : Term) → Value (ƛ N)
  Λ_ : {V : Term} → Value V → Value (Λ V)
  $ : (k : Const) → Value ($ k)
  _⟨_⟩ : {V : Term}{c : Coercion} → Value V → Inert c → Value (V ⟨ c ⟩)

------------------------------------------------------------------------
-- Type-variable substitution
------------------------------------------------------------------------

renameᵗᵐ : Renameᵗ → Term → Term
renameᵗᵐ ρ (` x) = ` x
renameᵗᵐ ρ (ƛ M) = ƛ renameᵗᵐ ρ M
renameᵗᵐ ρ (L · M) = renameᵗᵐ ρ L · renameᵗᵐ ρ M
renameᵗᵐ ρ (Λ M) = Λ (renameᵗᵐ (extᵗ ρ) M)
renameᵗᵐ ρ (ν A · L •⟨ c ⟩) =
  ν (renameᵗ ρ A) · (renameᵗᵐ ρ L) •⟨ renameᶜ (extᵗ ρ) c ⟩
renameᵗᵐ ρ ($ κ) = $ κ
renameᵗᵐ ρ (L ⊕[ op ] M) = renameᵗᵐ ρ L ⊕[ op ] renameᵗᵐ ρ M
renameᵗᵐ ρ (M ⟨ c ⟩) = renameᵗᵐ ρ M ⟨ renameᶜ ρ c ⟩
renameᵗᵐ ρ blame = blame

⇑ᵗᵐ : Term → Term
⇑ᵗᵐ = renameᵗᵐ suc

infixl 8 _[_]ᵀ
_[_]ᵀ : Term → TyVar → Term
M [ X ]ᵀ = renameᵗᵐ (singleRenameᵗ X) M

------------------------------------------------------------------------
-- Term-variable substitution
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

Subst : Set
Subst = Var → Term

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Term → Term
rename ρ (` x) = ` (ρ x)
rename ρ (ƛ M) = ƛ rename (ext ρ) M
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (Λ M) = Λ (rename ρ M)
rename ρ (ν A · L •⟨ c ⟩) = ν A · (rename ρ L) •⟨ c ⟩
rename ρ ($ κ) = $ κ
rename ρ (L ⊕[ op ] M) = rename ρ L ⊕[ op ] rename ρ M
rename ρ (M ⟨ c ⟩) = rename ρ M ⟨ c ⟩
rename ρ blame = blame

exts : Subst → Subst
exts σ zero = ` zero
exts σ (suc x) = rename suc (σ x)

↑ : Subst → Subst
↑ σ x = renameᵗᵐ suc (σ x)

subst : Subst → Term → Term
subst σ (` x) = σ x
subst σ (ƛ M) = ƛ subst (exts σ) M
subst σ (L · M) = subst σ L · subst σ M
subst σ (Λ M) = Λ (subst (↑ σ) M)
subst σ (ν A · L •⟨ c ⟩) = ν A · (subst σ L) •⟨ c ⟩
subst σ ($ κ) = $ κ
subst σ (L ⊕[ op ] M) = subst σ L ⊕[ op ] subst σ M
subst σ (M ⟨ c ⟩) = subst σ M ⟨ c ⟩
subst σ blame = blame

singleSub : Term → Subst
singleSub N zero = N
singleSub N (suc x) = ` x

infixl 8 _[_]
_[_] : Term → Term → Term
M [ N ] = subst (singleSub N) M

--------------------------------------------------------------------------------
-- Typing
--------------------------------------------------------------------------------

infix  4 _∣_∣_⊢_⦂_

data _∣_∣_⊢_⦂_ (Δ : TyCtx) (Σ : TyStore) (Γ : Ctx) : Term → Ty → Set₁ where

  ⊢` : ∀ {x A}
     → Γ ∋ x ⦂ A
      ----------------------
     → Δ ∣ Σ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {M A B}
     → WfTy Δ A
     → Δ ∣ Σ ∣ (A ∷ Γ) ⊢ M ⦂ B
      ----------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (ƛ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {L M A B}
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ (A ⇒ B)
     → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
      -------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (L · M) ⦂ B

  ⊢Λ : ∀ {M A}
     → Value M
     → suc Δ ∣ ⟰ᵗ Σ ∣ ⤊ᵗ Γ ⊢ M ⦂ A
      ----------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢ν : ∀ {L A B C c μ}
     → WfTy Δ A
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ `∀ C
     → μ ∣ suc Δ ∣ (0 , ⇑ᵗ A) ∷ ⟰ᵗ Σ ⊢ c ∶ C =⇒ ⇑ᵗ B
      ----------------------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ ν A · L •⟨ c ⟩ ⦂ B

  ⊢$ : ∀ (κ : Const)
      -------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M}
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Σ ∣ Γ ⊢ M ⦂ (‵ `ℕ)
      -----------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

  ⊢⟨⟩ : ∀ {M A B c μ}
      → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
      → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
      -------------------------
      → Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢blame : ∀ {A}
      → WfTy Δ A
      -----------------------
      → Δ ∣ Σ ∣ Γ ⊢ blame ⦂ A
