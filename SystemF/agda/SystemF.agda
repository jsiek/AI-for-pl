module SystemF where

open import Data.List using (List; []; _∷_; map)
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma using (Σ)
open import Data.Nat using (ℕ; _<_; zero; suc)

------------------------------------------------------------------------
-- Variables and Type Contexts
------------------------------------------------------------------------

Var : Set
Var = ℕ

TyCtx : Set
TyCtx = ℕ

------------------------------------------------------------------------
-- Types and Term Contexts
------------------------------------------------------------------------

infixr 7 _⇒_
infix 6 `∀

data Ty : Set where
  `_  : Var → Ty
  `ℕ  : Ty
  _⇒_   : Ty → Ty → Ty
  `∀ : Ty → Ty

Ctx : Set
Ctx = List Ty

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _·[_]
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_ : Var → Term
  ƛ_⇒_ : Ty → Term → Term
  _·_ : Term → Term → Term
  `zero : Term
  `suc_ : Term → Term
  case_[zero⇒_|suc⇒_] : Term → Term → Term → Term
  Λ_ : Term → Term
  _·[_] : Term → Ty → Term

------------------------------------------------------------------------
-- Parallel substitution (1): Types into Types
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = Var → Var

Substᵗ : Set
Substᵗ = Var → Ty

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ 0    = 0
extᵗ ρ (suc i) = suc (ρ i)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (` i)    = ` (ρ i)
renameᵗ ρ `ℕ       = `ℕ
renameᵗ ρ (A ⇒ B)  = (renameᵗ ρ A) ⇒ (renameᵗ ρ B)
renameᵗ ρ (`∀ A)  = `∀ (renameᵗ (extᵗ ρ) A)

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ 0    = ` 0
extsᵗ σ (suc i) = renameᵗ suc (σ i)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (` i)    = σ i
substᵗ σ `ℕ       = `ℕ
substᵗ σ (A ⇒ B)  = (substᵗ σ A) ⇒ (substᵗ σ B)
substᵗ σ (`∀ A)  = `∀ (substᵗ (extsᵗ σ) A)

singleTyEnv : Ty → Substᵗ
singleTyEnv B 0    = B
singleTyEnv B (suc i) = ` i

_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

------------------------------------------------------------------------
-- Parallel substitution (2): Types into Terms
------------------------------------------------------------------------

renameᵀ : Renameᵗ → Term → Term
renameᵀ ρ (` i)                      = ` i
renameᵀ ρ (ƛ A ⇒ N)                  = ƛ (renameᵗ ρ A) ⇒ (renameᵀ ρ N)
renameᵀ ρ (L · M)                    = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ `zero                      = `zero
renameᵀ ρ (`suc M)                   = `suc (renameᵀ ρ M)
renameᵀ ρ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (renameᵀ ρ L) (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (Λ N)                      = Λ (renameᵀ (extᵗ ρ) N)
renameᵀ ρ (M ·[ A ])                 = renameᵀ ρ M ·[ renameᵗ ρ A ]

substᵀ : Substᵗ → Term → Term
substᵀ σ (` i)                      = ` i
substᵀ σ (ƛ A ⇒ N)                  = ƛ (substᵗ σ A) ⇒ (substᵀ σ N)
substᵀ σ (L · M)                    = substᵀ σ L · substᵀ σ M
substᵀ σ `zero                      = `zero
substᵀ σ (`suc M)                   = `suc (substᵀ σ M)
substᵀ σ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (substᵀ σ L) (substᵀ σ M) (substᵀ σ N)
substᵀ σ (Λ N)                      = Λ (substᵀ (extsᵗ σ) N)
substᵀ σ (M ·[ A ])                 = substᵀ σ M ·[ substᵗ σ A ]

_[_]ᵀ : Term → Ty → Term
N [ A ]ᵀ = substᵀ (singleTyEnv A) N

------------------------------------------------------------------------
-- Parallel substitution (3): Terms into Terms
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

Subst : Set
Subst = Var → Term

ext : Rename → Rename
ext ρ 0    = 0
ext ρ (suc i) = suc (ρ i)

rename : Rename → Term → Term
rename ρ (` i)                      = ` (ρ i)
rename ρ (ƛ A ⇒ N)                  = ƛ A ⇒ rename (ext ρ) N
rename ρ (L · M)                    = rename ρ L · rename ρ M
rename ρ `zero                      = `zero
rename ρ (`suc M)                   = `suc (rename ρ M)
rename ρ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (Λ N)                      = Λ (rename ρ N)
rename ρ (M ·[ A ])                 = rename ρ M ·[ A ]

exts : Subst → Subst
exts σ 0    = ` 0
exts σ (suc i) = rename suc (σ i)

⇑ : Subst → Subst
⇑ σ i = renameᵀ suc (σ i)

subst : Subst → Term → Term
subst σ (` i)                      = σ i
subst σ (ƛ A ⇒ N)                  = ƛ A ⇒ subst (exts σ) N
subst σ (L · M)                    = subst σ L · subst σ M
subst σ `zero                      = `zero
subst σ (`suc M)                   = `suc (subst σ M)
subst σ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (Λ N)                      = Λ (subst (⇑ σ) N)
subst σ (M ·[ A ])                 = subst σ M ·[ A ]

singleEnv : Term → Subst
singleEnv M 0    = M
singleEnv M (suc i) = ` i

_[_] : Term → Term → Term
N [ M ] = subst (singleEnv M) N

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

⤊ : Ctx → Ctx
⤊ Γ = map (renameᵗ suc) Γ

data WfTy : Var → Ty → Set where
  wfVar  : {Δ : TyCtx}{X : Var} → X < Δ → WfTy Δ (` X)
  wf`ℕ  : {Δ : TyCtx} → WfTy Δ `ℕ
  wfFn   : {Δ : TyCtx} {A B : Ty} → WfTy Δ A → WfTy Δ B → WfTy Δ (A ⇒ B)
  wf`∀ : {Δ : TyCtx} {A : Ty} → WfTy (suc Δ) A → WfTy Δ (`∀ A)

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → Var → Ty → Set where
  Z : {Γ : Ctx} {A : Ty} →
      (A ∷ Γ) ∋ 0 ⦂ A
  S : {Γ : Ctx} {A B : Ty} {x : Var} →
      Γ ∋ x ⦂ A →
      (B ∷ Γ) ∋ suc x ⦂ A

infix 4 _⊢_⊢_⦂_
data _⊢_⊢_⦂_ : TyCtx → Ctx → Term → Ty → Set where
  ⊢` : {Δ : TyCtx} {Γ : Ctx} {i : Var} {A : Ty} →
       Γ ∋ i ⦂ A →
       Δ ⊢ Γ ⊢ (` i) ⦂ A

  ⊢ƛ : {Δ : TyCtx} {Γ : Ctx} {A B : Ty} {N : Term} →
       WfTy Δ A →
       Δ ⊢ (A ∷ Γ) ⊢ N ⦂ B →
       Δ ⊢ Γ ⊢ (ƛ A ⇒ N) ⦂ (A ⇒ B)

  ⊢· : {Δ : TyCtx} {Γ : Ctx} {A B : Ty} {L M : Term} →
       Δ ⊢ Γ ⊢ L ⦂ (A ⇒ B) →
       Δ ⊢ Γ ⊢ M ⦂ A →
       Δ ⊢ Γ ⊢ (L · M) ⦂ B

  ⊢zero : {Δ : TyCtx} {Γ : Ctx} →
          Δ ⊢ Γ ⊢ `zero ⦂ `ℕ

  ⊢suc : {Δ : TyCtx} {Γ : Ctx} {M : Term} →
         Δ ⊢ Γ ⊢ M ⦂ `ℕ →
         Δ ⊢ Γ ⊢ (`suc M) ⦂ `ℕ

  ⊢case : {Δ : TyCtx} {Γ : Ctx} {A : Ty} {L M N : Term} →
          Δ ⊢ Γ ⊢ L ⦂ `ℕ →
          Δ ⊢ Γ ⊢ M ⦂ A →
          Δ ⊢ (`ℕ ∷ Γ) ⊢ N ⦂ A →
          Δ ⊢ Γ ⊢ (case_[zero⇒_|suc⇒_] L M N) ⦂ A

  ⊢Λ : {Δ : TyCtx} {Γ : Ctx} {N : Term} {A : Ty} →
       (suc Δ) ⊢ (⤊ Γ) ⊢ N ⦂ A →
       Δ ⊢ Γ ⊢ (Λ N) ⦂ (`∀ A)

  ⊢·[] : {Δ : TyCtx} {Γ : Ctx} {M : Term} {A B : Ty} →
         Δ ⊢ Γ ⊢ M ⦂ (`∀ A) →
         WfTy Δ B →
         Δ ⊢ Γ ⊢ (M ·[ B ]) ⦂ A [ B ]ᵗ

------------------------------------------------------------------------
-- Reduction
------------------------------------------------------------------------

data Value : Term → Set where
  vLam  : {A : Ty} {N : Term} → Value (ƛ A ⇒ N)
  vZero : Value `zero
  vSuc  : {V : Term} → Value V → Value (`suc V)
  vTlam : {N : Term} → Value (Λ N)

infix 2 _—→_
data _—→_ : Term → Term → Set where
  ξ-·₁ : {L L' M : Term} →
         L —→ L' →
         (L · M) —→ (L' · M)

  ξ-·₂ : {V M M' : Term} →
         Value V →
         M —→ M' →
         (V · M) —→ (V · M')

  β-ƛ : {A : Ty} {N W : Term} →
        Value W →
        ((ƛ A ⇒ N) · W) —→ N [ W ]

  ξ-suc : {M M' : Term} →
          M —→ M' →
          (`suc M) —→ (`suc M')

  ξ-case : {L L' M N : Term} →
           L —→ L' →
           (case_[zero⇒_|suc⇒_] L M N) —→ (case_[zero⇒_|suc⇒_] L' M N)

  β-zero : {M N : Term} →
           (case_[zero⇒_|suc⇒_] `zero M N) —→ M

  β-suc : {V M N : Term} →
          Value V →
          (case_[zero⇒_|suc⇒_] (`suc V) M N) —→ N [ V ]

  ξ-·[] : {M M' : Term} {A : Ty} →
          M —→ M' →
          M ·[ A ] —→ M' ·[ A ]

  β-Λ : {N : Term} {A : Ty} →
        (Λ N) ·[ A ] —→ N [ A ]ᵀ

infix 3 _∎
infixr 2 _—→⟨_⟩_
infix 2 _—↠_
data _—↠_ : Term → Term → Set where
  _∎ : (M : Term) → M —↠ M
  _—→⟨_⟩_ : (L : Term) {M N : Term} → L —→ M → M —↠ N → L —↠ N

multi-trans : {M N L : Term} → M —↠ N → N —↠ L → M —↠ L
multi-trans (_ ∎) ms2          = ms2
multi-trans (_ —→⟨ s ⟩ ms1') ms2    = _ —→⟨ s ⟩ (multi-trans ms1' ms2)

infixr 2 _—↠⟨_⟩_
_—↠⟨_⟩_ : ∀ (L : Term) {M N : Term}
    → L —↠ M
    → M —↠ N
      ---------
    → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = multi-trans L—↠M M—↠N
