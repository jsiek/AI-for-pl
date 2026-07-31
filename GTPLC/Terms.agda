module Terms where

-- File Charter:
--   * Canonical syntax, values, runtime invariants, variable actions, and
--     typing for GTPLC terms.
--   * `TypingEnv` bundles the type context, type store, and term context.
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

record TypingEnv : Set where
  constructor ⟨_,_,_⟩
  field
    Δᵉ : TyCtx
    Σᵉ : TyStore
    Γᵉ : Ctx

open TypingEnv public

infixl 5 _,ᶜ_
infixl 5 _,ˢ_
infix 4 _⊢ᵀ_
infix 4 _∋ᵗ_⦂_
infix 4 _∣_⊢ᶜ_∶_=⇒_

_,ᶜ_ : TypingEnv → Ty → TypingEnv
⟨ Δ , Σ , Γ ⟩ ,ᶜ A = ⟨ Δ , Σ , A ∷ Γ ⟩

_,ˢ_ : TypingEnv → TyVar × Ty → TypingEnv
⟨ Δ , Σ , Γ ⟩ ,ˢ e = ⟨ Δ , e ∷ Σ , Γ ⟩

⇑ᵉᵗ : TypingEnv → TypingEnv
⇑ᵉᵗ ⟨ Δ , Σ , Γ ⟩ = ⟨ suc Δ , ⟰ᵗ Σ , ⤊ᵗ Γ ⟩

_⊢ᵀ_ : TypingEnv → Ty → Set
⟨ Δ , Σ , Γ ⟩ ⊢ᵀ A = WfTy Δ A

_∋ᵗ_⦂_ : TypingEnv → Var → Ty → Set₁
⟨ Δ , Σ , Γ ⟩ ∋ᵗ x ⦂ A = Γ ∋ x ⦂ A

_∣_⊢ᶜ_∶_=⇒_ :
  ModeEnv → TypingEnv → Coercion → Ty → Ty → Set
μ ∣ ⟨ Δ , Σ , Γ ⟩ ⊢ᶜ c ∶ A =⇒ B =
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B

private
  variable
    Ξ : TypingEnv
    L L′ M M′ N N′ V V′ : Term
    A A′ B B′ C C′ D D′ : Ty
    c d : Coercion
    μ : ModeEnv

infix 4 _⊢_⦂_

data _⊢_⦂_ : TypingEnv → Term → Ty → Set₁ where

  ⊢` : ∀ {x}
     → Ξ ∋ᵗ x ⦂ A
      ----------------
     → Ξ ⊢ (` x) ⦂ A

  ⊢ƛ : Ξ ⊢ᵀ A
     → Ξ ,ᶜ A ⊢ M ⦂ B
      --------------------
     → Ξ ⊢ (ƛ M) ⦂ (A ⇒ B)

  ⊢· : Ξ ⊢ L ⦂ (A ⇒ B)
     → Ξ ⊢ M ⦂ A
      -----------------
     → Ξ ⊢ (L · M) ⦂ B

  ⊢Λ : Value M
     → ⇑ᵉᵗ Ξ ⊢ M ⦂ A
      --------------------
     → Ξ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢ν : Ξ ⊢ᵀ A
     → Ξ ⊢ L ⦂ `∀ C
     → μ ∣ (⇑ᵉᵗ Ξ ,ˢ (zero , ⇑ᵗ A)) ⊢ᶜ c ∶ C =⇒ ⇑ᵗ B
      ----------------------------------------------
     → Ξ ⊢ ν A · L •⟨ c ⟩ ⦂ B

  ⊢$ : ∀ (κ : Const)
      -----------------------
     → Ξ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : Ξ ⊢ L ⦂ (‵ `ℕ)
     → (op : Prim)
     → Ξ ⊢ M ⦂ (‵ `ℕ)
      ---------------------------
     → Ξ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

  ⊢⟨⟩ : μ ∣ Ξ ⊢ᶜ c ∶ A =⇒ B
      → Ξ ⊢ M ⦂ A
      -----------------
      → Ξ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢blame :
        Ξ ⊢ᵀ A
      ---------------
      → Ξ ⊢ blame ⦂ A
