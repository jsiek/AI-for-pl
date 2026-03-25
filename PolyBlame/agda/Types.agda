module Types where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; _<_; zero; suc)

------------------------------------------------------------------------
-- Variables, contexts, base types
------------------------------------------------------------------------

Var : Set
Var = ℕ

TyVar : Set
TyVar = ℕ

Seal : Set
Seal = ℕ

TyCtx : Set
TyCtx = ℕ

data Base : Set where
  `ℕ    : Base
  `𝔹 : Base

infixr 7 _⇒_
infix  6 `∀

data Ty : Set where
  ＇_ : TyVar → Ty
  ｀_ : Seal → Ty
  ‵_ : Base → Ty
  `★  : Ty
  _⇒_ : Ty → Ty → Ty
  `∀  : Ty → Ty

Ctx : Set
Ctx = List Ty

Store : Set
Store = List Ty

extendStore : Store → Ty → Store
extendStore Σ A = Σ ++ (A ∷ [])

fresh : Store → Seal
fresh Σ = length Σ

------------------------------------------------------------------------
-- Type-variable substitution (de Bruijn X)
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = TyVar → TyVar

Substᵗ : Set
Substᵗ = TyVar → Ty

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ zero    = zero
extᵗ ρ (suc X) = suc (ρ X)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (＇ X)   = ＇ (ρ X)
renameᵗ ρ (｀ α)   = ｀ α
renameᵗ ρ (‵ ι)   = ‵ ι
renameᵗ ρ `★       = `★
renameᵗ ρ (A ⇒ B)  = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A)   = `∀ (renameᵗ (extᵗ ρ) A)

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ zero    = ＇ zero
extsᵗ σ (suc X) = renameᵗ suc (σ X)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (＇ X)   = σ X
substᵗ σ (｀ α)   = ｀ α
substᵗ σ (‵ ι)   = ‵ ι
substᵗ σ `★       = `★
substᵗ σ (A ⇒ B)  = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A)   = `∀ (substᵗ (extsᵗ σ) A)

singleTyEnv : Ty → Substᵗ
singleTyEnv B zero    = B
singleTyEnv B (suc X) = ＇ X

_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

infixl 8 _[_]ˢ

------------------------------------------------------------------------
-- Context lifting for type-variable binders
------------------------------------------------------------------------

⤊ : Ctx → Ctx
⤊ Γ = map (renameᵗ suc) Γ

renameStoreᵗ : Renameᵗ → Store → Store
renameStoreᵗ ρ []        = []
renameStoreᵗ ρ (A ∷ Σ)   = renameᵗ ρ A ∷ renameStoreᵗ ρ Σ

------------------------------------------------------------------------
-- Seal-variable renaming/opening (for ν binders over α)
------------------------------------------------------------------------

Renameˢ : Set
Renameˢ = Seal → Seal

extˢ : Renameˢ → Renameˢ
extˢ ρ zero    = zero
extˢ ρ (suc α) = suc (ρ α)

singleSealEnv : Seal → Renameˢ
singleSealEnv α zero    = α
singleSealEnv α (suc α') = α'

renameˢ : Renameˢ → Ty → Ty
renameˢ ρ (＇ X)   = ＇ X
renameˢ ρ (｀ α)   = ｀ (ρ α)
renameˢ ρ (‵ ι)   = ‵ ι
renameˢ ρ `★       = `★
renameˢ ρ (A ⇒ B)  = renameˢ ρ A ⇒ renameˢ ρ B
renameˢ ρ (`∀ A)   = `∀ (renameˢ ρ A)

⤊ˢ : Ctx → Ctx
⤊ˢ Γ = map (renameˢ suc) Γ

renameStoreˢ : Renameˢ → Store → Store
renameStoreˢ ρ [] = []
renameStoreˢ ρ (A ∷ Σ) =
  renameˢ ρ A ∷ renameStoreˢ ρ Σ

_[_]ˢ : Ty → Seal → Ty
A [ α ]ˢ = renameˢ (singleSealEnv α) A

------------------------------------------------------------------------
-- Well-formedness and lookup
------------------------------------------------------------------------

infix 4 _∋_⦂_
infix 4 _∋ˢ_⦂_

data _∋_⦂_ : Ctx → Var → Ty → Set where
  Z : {Γ : Ctx} {A : Ty} →
      (A ∷ Γ) ∋ zero ⦂ A
  S : {Γ : Ctx} {A B : Ty} {x : Var} →
      Γ ∋ x ⦂ A →
      (B ∷ Γ) ∋ suc x ⦂ A

data _∋ˢ_⦂_ : Store → Seal → Ty → Set where
  Zˢ : {Σ : Store} {A : Ty} →
       (A ∷ Σ) ∋ˢ zero ⦂ A
  Sˢ : {Σ : Store} {α : Seal} {A B : Ty} →
       Σ ∋ˢ α ⦂ A →
       (B ∷ Σ) ∋ˢ suc α ⦂ A

lookupˢ-extend :
  {Σ : Store} {α : Seal} {A B : Ty} →
  Σ ∋ˢ α ⦂ A →
  extendStore Σ B ∋ˢ α ⦂ A
lookupˢ-extend Zˢ = Zˢ
lookupˢ-extend (Sˢ h) = Sˢ (lookupˢ-extend h)

lookupˢ-fresh-extend :
  {Σ : Store} {B : Ty} →
  extendStore Σ B ∋ˢ fresh Σ ⦂ B
lookupˢ-fresh-extend {Σ = []} {B = B} = Zˢ
lookupˢ-fresh-extend {Σ = A ∷ Σ} {B = B} =
  Sˢ (lookupˢ-fresh-extend {Σ = Σ} {B = B})

data WfTy : TyCtx → Store → Ty → Set where
  wfX  : {Δ : TyCtx} {Σ : Store} {X : TyVar} →
         X < Δ →
         WfTy Δ Σ (＇ X)

  wfα  : {Δ : TyCtx} {Σ : Store} {α : Seal} {A : Ty} →
         Σ ∋ˢ α ⦂ A →
         WfTy Δ Σ (｀ α)

  wfι  : {Δ : TyCtx} {Σ : Store} {ι : Base} →
         WfTy Δ Σ (‵ ι)

  wf★  : {Δ : TyCtx} {Σ : Store} →
         WfTy Δ Σ `★

  wf⇒  : {Δ : TyCtx} {Σ : Store} {A B : Ty} →
         WfTy Δ Σ A →
         WfTy Δ Σ B →
         WfTy Δ Σ (A ⇒ B)

  wf∀  : {Δ : TyCtx} {Σ : Store} {A : Ty} →
         WfTy (suc Δ) (renameStoreᵗ suc Σ) A →
         WfTy Δ Σ (`∀ A)

