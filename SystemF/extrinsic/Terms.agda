module extrinsic.Terms where

-- File Charter:
--   * Core extrinsic System F syntax and static semantics.
--   * Defines terms, renaming/substitution, and typing.
--   * Keeps `renameᵀ`/`substᵀ` as identity-on-terms by design.

open import Data.List using (_∷_)
open import Data.Nat using (suc)
open import extrinsic.Types public

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_
infix  5 Λ_
infixl 7 _·_
infixl 7 _·[]
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_ : Var → Term
  ƛ_ : Term → Term
  _·_ : Term → Term → Term
  `true : Term
  `false : Term
  `zero : Term
  `suc_ : Term → Term
  case_[zero⇒_|suc⇒_] : Term → Term → Term → Term
  `if_then_else : Term → Term → Term → Term
  Λ_ : Term → Term
  _·[] : Term → Term

------------------------------------------------------------------------
-- Design note: type-into-term renaming/substitution
------------------------------------------------------------------------
--
-- In this `extrinsic` System F development, `renameᵀ` and `substᵀ`
-- are intentionally defined as identities. This is a deliberate
-- deviation from the usual System F pattern where type-level
-- substitutions act structurally on terms.
--
-- Motivation: keep the metatheory simpler in this formulation,
-- especially for relational parametricity proofs (in particular, the
-- fundamental theorem).

renameᵀ : Renameᵗ → Term → Term
renameᵀ ρ M = M

substᵀ : Substᵗ → Term → Term
substᵀ σ M = M

_[_]ᵀ : Term → Ty → Term
N [ A ]ᵀ = N

------------------------------------------------------------------------
-- Parallel substitution: Terms into Terms
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
rename ρ (ƛ N)                      = ƛ (rename (ext ρ) N)
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
rename ρ (M ·[])                    = rename ρ M ·[]

exts : Subst → Subst
exts σ 0    = ` 0
exts σ (suc i) = rename suc (σ i)

⇑ : Subst → Subst
⇑ σ i = renameᵀ suc (σ i)

subst : Subst → Term → Term
subst σ (` i)                      = σ i
subst σ (ƛ N)                      = ƛ (subst (exts σ) N)
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
subst σ (M ·[])                    = subst σ M ·[]

singleEnv : Term → Subst
singleEnv M 0    = M
singleEnv M (suc i) = ` i

_[_] : Term → Term → Term
N [ M ] = subst (singleEnv M) N

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _⊢_⊢_⦂_
data _⊢_⊢_⦂_ : TyCtx → Ctx → Term → Ty → Set where
  ⊢` : {Δ : TyCtx} {Γ : Ctx} {i : Var} {A : Ty} →
       Γ ∋ i ⦂ A →
       Δ ⊢ Γ ⊢ (` i) ⦂ A

  ⊢ƛ : {Δ : TyCtx} {Γ : Ctx} {A B : Ty} {N : Term} →
       WfTy Δ A →
       Δ ⊢ (A ∷ Γ) ⊢ N ⦂ B →
       Δ ⊢ Γ ⊢ (ƛ N) ⦂ (A ⇒ B)

  ⊢· : {Δ : TyCtx} {Γ : Ctx} {A B : Ty} {L M : Term} →
       Δ ⊢ Γ ⊢ L ⦂ (A ⇒ B) →
       Δ ⊢ Γ ⊢ M ⦂ A →
       Δ ⊢ Γ ⊢ (L · M) ⦂ B

  ⊢true : {Δ : TyCtx} {Γ : Ctx} →
          Δ ⊢ Γ ⊢ `true ⦂ `Bool

  ⊢false : {Δ : TyCtx} {Γ : Ctx} →
           Δ ⊢ Γ ⊢ `false ⦂ `Bool

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

  ⊢if : {Δ : TyCtx} {Γ : Ctx} {A : Ty} {L M N : Term} →
        Δ ⊢ Γ ⊢ L ⦂ `Bool →
        Δ ⊢ Γ ⊢ M ⦂ A →
        Δ ⊢ Γ ⊢ N ⦂ A →
        Δ ⊢ Γ ⊢ (`if_then_else L M N) ⦂ A

  ⊢Λ : {Δ : TyCtx} {Γ : Ctx} {N : Term} {A : Ty} →
       (suc Δ) ⊢ (⤊ Γ) ⊢ N ⦂ A →
       Δ ⊢ Γ ⊢ (Λ N) ⦂ (`∀ A)

  ⊢·[] : {Δ : TyCtx} {Γ : Ctx} {M : Term} {A B : Ty} →
         Δ ⊢ Γ ⊢ M ⦂ (`∀ A) →
         WfTy Δ B →
         Δ ⊢ Γ ⊢ (M ·[]) ⦂ A [ B ]ᵗ
