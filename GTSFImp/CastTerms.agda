module CastTerms where

-- File Charter:
--   * 

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

open import Types
open import TyStore
open import TermCtx
open import Primitives
open import Imprecision

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_
infixl 7 _·_
infix  5 Λ_
infix  7 _•_
infixl 7 _⟨_⇒_⟩
infixl 6 _⊕[_]_
infix  9 `_

Var : Set
Var = ℕ

data Term : Set where
  `_      : Var → Term
  ƛ_      : Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _•_     : Term → Ty → Term
  $       : Const → Term
  _⊕[_]_  : Term → Prim → Term → Term
  _⟨_⇒_⟩  : Term → Ty → Ty → Term
  seal    : Term → TyVar → Term
  unseal  : Term → TyVar → Term
  blame   : Term

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Inert : Ty → Ty → Set where
  inj : ∀{A} → A ≢ ★ → Inert A ★
  gen : ∀{A B} → A ≢ ★ → Inert A (`∀ B)
  fun : ∀{A A′ B B′} → Inert (A ⇒ B) (A′ ⇒ B′)

data Value : Term → Set where
  ƛ_ : (N : Term) → Value (ƛ N)
  Λ_ : {V : Term} → Value V → Value (Λ V)
  $ : (k : Const) → Value ($ k)
  seal : {V : Term} → Value V → (X : TyVar) → Value (seal V X)
  _《_》 : {V : Term}{A B : Ty} → Value V → Inert A B → Value (V ⟨ A ⇒ B ⟩)

--------------------------------------------------------------------------------
-- Typing
--------------------------------------------------------------------------------

record Ctx : Set where
  constructor ⟨_,_,_⟩
  field
    Δᵉ : TyCtx
    Σᵉ : TyStore
    Γᵉ : TermCtx

open Ctx public

infixl 5 _,ᶜ_
infixl 5 _,ˢ_
infix 4 _⊢ᵀ_
infix 4 _∋ᵗ_⦂_

_,ᶜ_ : Ctx → Ty → Ctx
⟨ Δ , Σ , Γ ⟩ ,ᶜ A = ⟨ Δ , Σ , A ∷ Γ ⟩

_,ˢ_ : Ctx → TyVar × Ty → Ctx
⟨ Δ , Σ , Γ ⟩ ,ˢ e = ⟨ Δ , e ∷ Σ , Γ ⟩

⇑ᵉᵗ : Ctx → Ctx
⇑ᵉᵗ ⟨ Δ , Σ , Γ ⟩ = ⟨ suc Δ , ⟰ᵗ Σ , ⤊ᵗ Γ ⟩

_⊢ᵀ_ : Ctx → Ty → Set
⟨ Δ , Σ , Γ ⟩ ⊢ᵀ A = WfTy Δ A

_∋ᵗ_⦂_ : Ctx → Var → Ty → Set₁
⟨ Δ , Σ , Γ ⟩ ∋ᵗ x ⦂ A = Γ ∋ x ⦂ A

_⊢ᵀ_⊑_ : Ctx → Ty → Ty → Set
⟨ Δ , Σ , Γ ⟩ ⊢ᵀ A ⊑ B = Δ ⊢ A ⊑ B

private
  variable
    Γ : Ctx
    X Y : TyVar
    A A′ B B′ C C′ D D′ : Ty
    L L′ M M′ N N′ V V′ : Term

infix 4 _⊢_⦂_

data _⊢_⦂_ : Ctx → Term → Ty → Set₁ where

  ⊢` : ∀ {x}
     → Γ ∋ᵗ x ⦂ A
      ----------------
     → Γ ⊢ (` x) ⦂ A

  ⊢ƛ : Γ ⊢ᵀ A
     → Γ ,ᶜ A ⊢ M ⦂ B
      --------------------
     → Γ ⊢ (ƛ M) ⦂ (A ⇒ B)

  ⊢· : Γ ⊢ L ⦂ (A ⇒ B)
     → Γ ⊢ M ⦂ A
      -----------------
     → Γ ⊢ (L · M) ⦂ B

  ⊢Λ : Value M
     → ⇑ᵉᵗ Γ ⊢ M ⦂ A
      --------------------
     → Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : Γ ⊢ L ⦂ `∀ C
     → Γ ⊢ᵀ A
      ----------------------
     → Γ ⊢ L • A ⦂ C [ A ]ᵗ

  ⊢$ : ∀ (κ : Const)
      -----------------------
     → Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : Γ ⊢ L ⦂ (‵ `ℕ)
     → (op : Prim)
     → Γ ⊢ M ⦂ (‵ `ℕ)
      ---------------------------
     → Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

  ⊢⟨⇒⟩ : 
        Γ ⊢ M ⦂ A
      → Γ ⊢ᵀ B ⊑ A
      → Γ ⊢ᵀ B ⊑ C
      ---------------------
      → Γ ⊢ M ⟨ A ⇒ C ⟩ ⦂ C

  ⊢seal : 
        Γ ⊢ M ⦂ A
      → Γ ∋ᵗ X ⦂ A
      ---------------------
      → Γ ⊢ seal M X ⦂ ＇ X

  ⊢unseal : 
        Γ ⊢ M ⦂ ＇ X
      → Γ ∋ᵗ X ⦂ A
      ---------------------
      → Γ ⊢ unseal M X ⦂ A

  ⊢blame :
        Γ ⊢ᵀ A
      ---------------
      → Γ ⊢ blame ⦂ A

------------------------------------------------------------------------
-- Type-variable renaming
------------------------------------------------------------------------

renameᵗᵐ : Renameᵗ → Term → Term
renameᵗᵐ ρ (` x) = ` x
renameᵗᵐ ρ (ƛ M) = ƛ renameᵗᵐ ρ M
renameᵗᵐ ρ (L · M) = renameᵗᵐ ρ L · renameᵗᵐ ρ M
renameᵗᵐ ρ (Λ M) = Λ (renameᵗᵐ (extᵗ ρ) M)
renameᵗᵐ ρ (L • A) = (renameᵗᵐ ρ L) • (renameᵗ ρ A)
renameᵗᵐ ρ ($ κ) = $ κ
renameᵗᵐ ρ (L ⊕[ op ] M) = renameᵗᵐ ρ L ⊕[ op ] renameᵗᵐ ρ M
renameᵗᵐ ρ (M ⟨ A ⇒ B ⟩) = renameᵗᵐ ρ M ⟨ renameᵗ ρ A ⇒ renameᵗ ρ B ⟩
renameᵗᵐ ρ (seal M X) = seal (renameᵗᵐ ρ M) (ρ X)
renameᵗᵐ ρ (unseal M X) = unseal (renameᵗᵐ ρ M) (ρ X)
renameᵗᵐ ρ blame = blame

⇑ᵗᵐ : Term → Term
⇑ᵗᵐ = renameᵗᵐ suc

infixl 8 _[_]ᵀ
_[_]ᵀ : Term → TyVar → Term
M [ X ]ᵀ = renameᵗᵐ (singleRenameᵗ X) M

------------------------------------------------------------------------
-- Term-variable renaming
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Term → Term
rename ρ (` x) = ` (ρ x)
rename ρ (ƛ M) = ƛ rename (ext ρ) M
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (Λ M) = Λ (rename ρ M)
rename ρ (L • A) = (rename ρ L) • A
rename ρ ($ κ) = $ κ
rename ρ (L ⊕[ op ] M) = rename ρ L ⊕[ op ] rename ρ M
rename ρ (M ⟨ A ⇒ B ⟩) = rename ρ M ⟨ A ⇒ B ⟩
rename ρ (seal M X) = seal (rename ρ M) X
rename ρ (unseal M X) = unseal (rename ρ M) X
rename ρ blame = blame

------------------------------------------------------------------------
-- Term-variable substitution
------------------------------------------------------------------------

Subst : Set
Subst = Var → Term

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
subst σ (L • A) = (subst σ L) • A
subst σ ($ κ) = $ κ
subst σ (L ⊕[ op ] M) = subst σ L ⊕[ op ] subst σ M
subst σ (M ⟨ A ⇒ B ⟩) = subst σ M ⟨ A ⇒ B ⟩
subst σ (seal M X) = seal (subst σ M) X
subst σ (unseal M X) = unseal (subst σ M) X
subst σ blame = blame

singleSub : Term → Subst
singleSub N zero = N
singleSub N (suc x) = ` x

infixl 8 _[_]
_[_] : Term → Term → Term
M [ N ] = subst (singleSub N) M
