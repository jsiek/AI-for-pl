module Types where

open import Data.List using (List; []; _∷_; map)
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
-- Parallel substitution on Types
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
-- Well-formed types and typed variable lookup
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
