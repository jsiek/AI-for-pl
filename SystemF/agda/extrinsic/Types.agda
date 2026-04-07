module extrinsic.Types where

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

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
  `Bool : Ty
  _⇒_   : Ty → Ty → Ty
  `∀ : Ty → Ty

infix 4 _≡ᵗ_
_≡ᵗ_ : Ty → Ty → Set
A ≡ᵗ B = A ≡ B

Ctx : Set
Ctx = List Ty

------------------------------------------------------------------------
-- Parallel substitution on Types
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = Var → Var

Substᵗ : Set
Substᵗ = Var → Ty

renᵗ : Renameᵗ → Substᵗ
renᵗ ρ i = ` (ρ i)

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ 0    = 0
extᵗ ρ (suc i) = suc (ρ i)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (` i)    = ` (ρ i)
renameᵗ ρ `ℕ       = `ℕ
renameᵗ ρ `Bool    = `Bool
renameᵗ ρ (A ⇒ B)  = (renameᵗ ρ A) ⇒ (renameᵗ ρ B)
renameᵗ ρ (`∀ A)  = `∀ (renameᵗ (extᵗ ρ) A)

⇑ᵗ : Ty → Ty
⇑ᵗ = renameᵗ suc

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ 0    = ` 0
extsᵗ σ (suc i) = ⇑ᵗ (σ i)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (` i)    = σ i
substᵗ σ `ℕ       = `ℕ
substᵗ σ `Bool    = `Bool
substᵗ σ (A ⇒ B)  = (substᵗ σ A) ⇒ (substᵗ σ B)
substᵗ σ (`∀ A)  = `∀ (substᵗ (extsᵗ σ) A)

substᵗ-cong : ∀ {σ τ : Substᵗ}
  → ((i : Var) → σ i ≡ τ i)
  → (A : Ty)
  → substᵗ σ A ≡ substᵗ τ A
substᵗ-cong h (` i) = h i
substᵗ-cong h `ℕ = refl
substᵗ-cong h `Bool = refl
substᵗ-cong h (A ⇒ B) = cong₂ _⇒_ (substᵗ-cong h A) (substᵗ-cong h B)
substᵗ-cong {σ} {τ} h (`∀ A) = cong `∀ (substᵗ-cong h-ext A)
  where
  h-ext : (i : Var) → extsᵗ σ i ≡ extsᵗ τ i
  h-ext zero = refl
  h-ext (suc i) = cong (renameᵗ suc) (h i)

extsᵗ-renᵗ : (ρ : Renameᵗ) → (i : Var) → extsᵗ (renᵗ ρ) i ≡ renᵗ (extᵗ ρ) i
extsᵗ-renᵗ ρ zero = refl
extsᵗ-renᵗ ρ (suc i) = refl

substᵗ-renᵗ : (ρ : Renameᵗ) (A : Ty) → substᵗ (renᵗ ρ) A ≡ renameᵗ ρ A
substᵗ-renᵗ ρ (` i) = refl
substᵗ-renᵗ ρ `ℕ = refl
substᵗ-renᵗ ρ `Bool = refl
substᵗ-renᵗ ρ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-renᵗ ρ A) (substᵗ-renᵗ ρ B)
substᵗ-renᵗ ρ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-cong (extsᵗ-renᵗ ρ) A)
      (substᵗ-renᵗ (extᵗ ρ) A))

singleTyEnv : Ty → Substᵗ
singleTyEnv B 0    = B
singleTyEnv B (suc i) = ` i

_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

idᵗ : Substᵗ
idᵗ = `_

infixr 6 _•ᵗ_
_•ᵗ_ : Ty → Substᵗ → Substᵗ
(A •ᵗ σ) zero      = A
(A •ᵗ σ) (suc α)  = σ α

substCtx : Substᵗ → Ctx → Ctx
substCtx σ []       = []
substCtx σ (A ∷ Γ) = substᵗ σ A ∷ substCtx σ Γ

------------------------------------------------------------------------
-- Well-formed types and typed variable lookup
------------------------------------------------------------------------

⤊ : Ctx → Ctx
⤊ Γ = map ⇑ᵗ Γ

data WfTy : Var → Ty → Set where
  wfVar  : {Δ : TyCtx}{X : Var} → X < Δ → WfTy Δ (` X)
  wf`ℕ  : {Δ : TyCtx} → WfTy Δ `ℕ
  wf`Bool : {Δ : TyCtx} → WfTy Δ `Bool
  wfFn   : {Δ : TyCtx} {A B : Ty} → WfTy Δ A → WfTy Δ B → WfTy Δ (A ⇒ B)
  wf`∀ : {Δ : TyCtx} {A : Ty} → WfTy (suc Δ) A → WfTy Δ (`∀ A)

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → Var → Ty → Set where
  Z : {Γ : Ctx} {A : Ty} →
      (A ∷ Γ) ∋ 0 ⦂ A
  S : {Γ : Ctx} {A B : Ty} {x : Var} →
      Γ ∋ x ⦂ A →
      (B ∷ Γ) ∋ suc x ⦂ A
