module extrinsic.Terms where

-- File Charter:
--   * Core extrinsic System F syntax and static semantics.
--   * Defines terms, renaming/substitution, and typing.
--   * Includes all three renaming/substitution actions:
--       (1) types in types, (2) types in terms, (3) terms in terms.

open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import extrinsic.Types public
open import extrinsic.TypeSubst as TS using ()

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _·[_]
infix  8 `suc_
infix  9 `_

-- Design decision:
--   We intentionally follow the standard System F concrete syntax:
--   λ-abstractions carry explicit type annotations (`ƛ[ A ] N`) and type
--   applications carry explicit instantiation types (`M ·[ A ]`).
--   We use bracketed lambda annotations to avoid parser overlap with
--   function types (`_⇒_`).

data Term : Set where
  `_ : Var → Term
  ƛ_⇒_ : Ty → Term → Term
  _·_ : Term → Term → Term
  `true : Term
  `false : Term
  `zero : Term
  `suc_ : Term → Term
  case_[zero⇒_|suc⇒_] : Term → Term → Term → Term
  `if_then_else : Term → Term → Term → Term
  Λ_ : Term → Term
  _·[_] : Term → Ty → Term

lam : Ty → Term → Term
lam = ƛ_⇒_

syntax lam A N = ƛ[ A ] N

------------------------------------------------------------------------
-- Parallel substitution: Types into Terms
------------------------------------------------------------------------

renameᵀ : Renameᵗ → Term → Term
renameᵀ ρ (` i)                      = ` i
renameᵀ ρ (ƛ A ⇒ N)                  = ƛ (renameᵗ ρ A) ⇒ (renameᵀ ρ N)
renameᵀ ρ (L · M)                    = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ `true                      = `true
renameᵀ ρ `false                     = `false
renameᵀ ρ `zero                      = `zero
renameᵀ ρ (`suc M)                   = `suc (renameᵀ ρ M)
renameᵀ ρ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (renameᵀ ρ L) (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (`if_then_else L M N)      =
  `if_then_else (renameᵀ ρ L) (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (Λ N)                      = Λ (renameᵀ (extᵗ ρ) N)
renameᵀ ρ (M ·[ A ])                 = renameᵀ ρ M ·[ renameᵗ ρ A ]

substᵀ : Substᵗ → Term → Term
substᵀ σ (` i)                      = ` i
substᵀ σ (ƛ A ⇒ N)                  = ƛ (substᵗ σ A) ⇒ (substᵀ σ N)
substᵀ σ (L · M)                    = substᵀ σ L · substᵀ σ M
substᵀ σ `true                      = `true
substᵀ σ `false                     = `false
substᵀ σ `zero                      = `zero
substᵀ σ (`suc M)                   = `suc (substᵀ σ M)
substᵀ σ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (substᵀ σ L) (substᵀ σ M) (substᵀ σ N)
substᵀ σ (`if_then_else L M N)      =
  `if_then_else (substᵀ σ L) (substᵀ σ M) (substᵀ σ N)
substᵀ σ (Λ N)                      = Λ (substᵀ (extsᵗ σ) N)
substᵀ σ (M ·[ A ])                 = substᵀ σ M ·[ substᵗ σ A ]

_[_]ᵀ : Term → Ty → Term
N [ A ]ᵀ = substᵀ (singleTyEnv A) N

------------------------------------------------------------------------
-- Parallel substitution: Terms into Terms
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

Subst : Set
Subst = Var → Term

ren : Rename → Subst
ren ρ i = ` (ρ i)

ext : Rename → Rename
ext ρ 0    = 0
ext ρ (suc i) = suc (ρ i)

rename : Rename → Term → Term
rename ρ (` i)                      = ` (ρ i)
rename ρ (ƛ A ⇒ N)                  = ƛ A ⇒ rename (ext ρ) N
rename ρ (L · M)                    = rename ρ L · rename ρ M
rename ρ `true                      = `true
rename ρ `false                     = `false
rename ρ `zero                      = `zero
rename ρ (`suc M)                   = `suc (rename ρ M)
rename ρ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (`if_then_else L M N)      =
  `if_then_else (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (Λ N)                      = Λ (rename ρ N)
rename ρ (M ·[ A ])                 = rename ρ M ·[ A ]

exts : Subst → Subst
exts σ 0    = ` 0
exts σ (suc i) = rename suc (σ i)

⇑ : Subst → Subst
⇑ σ i = renameᵀ suc (σ i)

⇑ᵀ : Subst → Subst
⇑ᵀ σ i = rename suc (σ i)

id : Subst
id x = ` x

_•_ : Term → Subst → Subst
(M • σ) 0       = M
(M • σ) (suc x) = σ x

subst : Subst → Term → Term
subst σ (` i)                      = σ i
subst σ (ƛ A ⇒ N)                  = ƛ A ⇒ subst (exts σ) N
subst σ (L · M)                    = subst σ L · subst σ M
subst σ `true                      = `true
subst σ `false                     = `false
subst σ `zero                      = `zero
subst σ (`suc M)                   = `suc (subst σ M)
subst σ (case_[zero⇒_|suc⇒_] L M N) =
  case_[zero⇒_|suc⇒_] (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (`if_then_else L M N)      =
  `if_then_else (subst σ L) (subst σ M) (subst σ N)
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

infix 4 _∣_⊢_⦂_
data _∣_⊢_⦂_ : TyCtx → Ctx → Term → Ty → Set where
  ⊢` : {Δ : TyCtx} {Γ : Ctx} {i : Var} {A : Ty} →
       Γ ∋ i ⦂ A →
       Δ ∣ Γ ⊢ (` i) ⦂ A

  ⊢ƛ : {Δ : TyCtx} {Γ : Ctx} {A B : Ty} {N : Term} →
       WfTy Δ A →
       Δ ∣ (A ∷ Γ) ⊢ N ⦂ B →
       Δ ∣ Γ ⊢ (ƛ A ⇒ N) ⦂ (A ⇒ B)

  ⊢· : {Δ : TyCtx} {Γ : Ctx} {A B : Ty} {L M : Term} →
       Δ ∣ Γ ⊢ L ⦂ (A ⇒ B) →
       Δ ∣ Γ ⊢ M ⦂ A →
       Δ ∣ Γ ⊢ (L · M) ⦂ B

  ⊢true : {Δ : TyCtx} {Γ : Ctx} →
          Δ ∣ Γ ⊢ `true ⦂ `Bool

  ⊢false : {Δ : TyCtx} {Γ : Ctx} →
           Δ ∣ Γ ⊢ `false ⦂ `Bool

  ⊢zero : {Δ : TyCtx} {Γ : Ctx} →
          Δ ∣ Γ ⊢ `zero ⦂ `ℕ

  ⊢suc : {Δ : TyCtx} {Γ : Ctx} {M : Term} →
         Δ ∣ Γ ⊢ M ⦂ `ℕ →
         Δ ∣ Γ ⊢ (`suc M) ⦂ `ℕ

  ⊢case : {Δ : TyCtx} {Γ : Ctx} {A : Ty} {L M N : Term} →
          Δ ∣ Γ ⊢ L ⦂ `ℕ →
          Δ ∣ Γ ⊢ M ⦂ A →
          Δ ∣ (`ℕ ∷ Γ) ⊢ N ⦂ A →
          Δ ∣ Γ ⊢ (case_[zero⇒_|suc⇒_] L M N) ⦂ A

  ⊢if : {Δ : TyCtx} {Γ : Ctx} {A : Ty} {L M N : Term} →
        Δ ∣ Γ ⊢ L ⦂ `Bool →
        Δ ∣ Γ ⊢ M ⦂ A →
        Δ ∣ Γ ⊢ N ⦂ A →
        Δ ∣ Γ ⊢ (`if_then_else L M N) ⦂ A

  ⊢Λ : {Δ : TyCtx} {Γ : Ctx} {N : Term} {A : Ty} →
       (suc Δ) ∣ (⤊ Γ) ⊢ N ⦂ A →
       Δ ∣ Γ ⊢ (Λ N) ⦂ (`∀ A)

  ⊢·[] : {Δ : TyCtx} {Γ : Ctx} {M : Term} {A B : Ty} →
         Δ ∣ Γ ⊢ M ⦂ (`∀ A) →
         WfTy Δ B →
         Δ ∣ Γ ⊢ (M ·[ B ]) ⦂ A [ B ]ᵗ
