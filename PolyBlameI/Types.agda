module Types where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst)

------------------------------------------------------------------------
-- Variables, contexts, base types
------------------------------------------------------------------------

Var : Set
Var = ℕ

TyCtx : Set
TyCtx = ℕ

data TyVar : (Δ : TyCtx) → Set where
  Zᵗ : ∀{Δ} → TyVar (suc Δ)
  Sᵗ : ∀{Δ}
     → TyVar Δ
       --------------
     → TyVar (suc Δ)

SealCtx : Set
SealCtx = ℕ

data Seal : (Ψ : SealCtx) → Set where
  Zˢ : ∀{Ψ} → Seal (suc Ψ)
  Sˢ : ∀{Ψ}
     → Seal Ψ
       --------------
     → Seal (suc Ψ)


data Base : Set where
  `ℕ    : Base
  `𝔹 : Base

infixr 7 _⇒_
infix  6 `∀

data Ty : TyCtx → SealCtx → Set where
  ＇_ : ∀{Δ}{Ψ} (X : TyVar Δ) → Ty Δ Ψ
  ｀_ : ∀{Δ}{Ψ} (α : Seal Ψ) → Ty Δ Ψ
  ‵_ : ∀{Δ}{Ψ} → Base → Ty Δ Ψ
  `★  : ∀{Δ}{Ψ} → Ty Δ Ψ
  _⇒_ : ∀{Δ}{Ψ} → Ty Δ Ψ → Ty Δ Ψ → Ty Δ Ψ
  `∀  : ∀{Δ}{Ψ} → Ty (suc Δ) Ψ → Ty Δ Ψ

data TVar : TyCtx → SealCtx → Set where
  ＇_ : ∀{Δ}{Ψ} (X : TyVar Δ) → TVar Δ Ψ
  ｀_ : ∀{Δ}{Ψ} (α : Seal Ψ) → TVar Δ Ψ

tvTy : ∀{Δ}{Ψ} → TVar Δ Ψ → Ty Δ Ψ
tvTy (＇ X) = ＇ X
tvTy (｀ α) = ｀ α

data Cross : ∀{Δ}{Ψ} → Ty Δ Ψ → Set where
  ＇_ : ∀{Δ}{Ψ} (X : TyVar Δ) → Cross{Δ}{Ψ} (＇ X)
  ｀_ : ∀{Δ}{Ψ} (α : Seal Ψ) → Cross{Δ}{Ψ} (｀ α)
  ‵_ : ∀{Δ}{Ψ} → (ι : Base) → Cross{Δ}{Ψ} (‵ ι)
  _⇒_ : ∀{Δ}{Ψ} → (A : Ty Δ Ψ) → (B : Ty Δ Ψ) → Cross (A ⇒ B)
  `∀  : ∀{Δ}{Ψ} → (A : Ty (suc Δ) Ψ) → Cross (`∀ A)

data Ground : ∀{Δ}{Ψ} → Ty Δ Ψ → Set where
  ｀_ : ∀{Δ}{Ψ} (α : Seal Ψ) → Ground{Δ}{Ψ} (｀ α)
  ‵_ : ∀{Δ}{Ψ} → (ι : Base) → Ground{Δ}{Ψ} (‵ ι)
  ★⇒★ : ∀{Δ}{Ψ} → Ground{Δ}{Ψ} (`★ ⇒ `★)

Ctx : TyCtx → SealCtx → Set
Ctx Δ Ψ = List (Ty Δ Ψ)

Store : SealCtx → Set
Store Ψ = List (Seal Ψ × Ty 0 Ψ)

∅ˢ : ∀{Ψ} → Store Ψ
∅ˢ = []

extendˢ : ∀{Ψ} → Store Ψ → Seal Ψ → Ty 0 Ψ → Store Ψ
extendˢ Σ α A = (α , A) ∷ Σ

------------------------------------------------------------------------
-- Type-variable substitution (de Bruijn X)
------------------------------------------------------------------------

Renameᵗ : TyCtx → TyCtx → Set
Renameᵗ Δ Δ′ = TyVar Δ → TyVar Δ′

Substᵗ : TyCtx → TyCtx → SealCtx → Set
Substᵗ Δ Δ′ Ψ = TyVar Δ → TVar Δ′ Ψ

extᵗ : ∀{Δ}{Δ′} → Renameᵗ Δ Δ′ → Renameᵗ (suc Δ) (suc Δ′)
extᵗ ρ Zᵗ = Zᵗ
extᵗ ρ (Sᵗ X) = Sᵗ (ρ X)

renameᵗⱽ : ∀ {Δ}{Δ′}{Ψ} → Renameᵗ Δ Δ′ → TVar Δ Ψ → TVar Δ′ Ψ
renameᵗⱽ ρ (＇ X) = ＇ (ρ X)
renameᵗⱽ ρ (｀ α) = ｀ α

renameᵗ : ∀ {Δ}{Δ′}{Ψ} → Renameᵗ Δ Δ′ → Ty Δ Ψ → Ty Δ′ Ψ
renameᵗ ρ (＇ X) = ＇ (ρ X)
renameᵗ ρ (｀ α) = ｀ α
renameᵗ ρ (‵ ι) = ‵ ι
renameᵗ ρ `★ = `★
renameᵗ ρ (A ⇒ B) = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A) = `∀ (renameᵗ (extᵗ ρ) A)

⇑ᵗⱽ : ∀{Δ}{Ψ} → TVar Δ Ψ → TVar (suc Δ) Ψ
⇑ᵗⱽ = renameᵗⱽ Sᵗ

extsᵗ : ∀ {Δ}{Δ′}{Ψ} → Substᵗ Δ Δ′ Ψ → Substᵗ (suc Δ) (suc Δ′) Ψ
extsᵗ σ Zᵗ    = ＇ Zᵗ
extsᵗ σ (Sᵗ X) = renameᵗⱽ Sᵗ (σ X)

substᵗ : ∀ {Δ}{Δ′}{Ψ} → Substᵗ Δ Δ′ Ψ → Ty Δ Ψ → Ty Δ′ Ψ
substᵗ σ (＇ X)   = tvTy (σ X)
substᵗ σ (｀ α)   = ｀ α
substᵗ σ (‵ ι)   = ‵ ι
substᵗ σ `★       = `★
substᵗ σ (A ⇒ B)  = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A)   = `∀ (substᵗ (extsᵗ σ) A)

singleTyEnv : ∀ {Δ}{Ψ} → TVar Δ Ψ → Substᵗ (suc Δ) Δ Ψ
singleTyEnv B Zᵗ    = B
singleTyEnv B (Sᵗ X) = ＇ X

infixl 8 _[_]ᵗ
_[_]ᵗ : ∀ {Δ}{Ψ} → Ty (suc Δ) Ψ → TVar Δ Ψ → Ty Δ Ψ
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

------------------------------------------------------------------------
-- Lift closed store types (Ty 0 Ψ) into an arbitrary Δ
------------------------------------------------------------------------

lift0ᵗ : ∀{Δ} → Renameᵗ 0 Δ
lift0ᵗ ()

wkTy0 : ∀{Δ}{Ψ} → Ty 0 Ψ → Ty Δ Ψ
wkTy0 = renameᵗ lift0ᵗ

------------------------------------------------------------------------
-- Seal-variable renaming/opening (for ν binders over α)
------------------------------------------------------------------------

Renameˢ : SealCtx → SealCtx → Set
Renameˢ Ψ Ψ′ = Seal Ψ → Seal Ψ′

extˢ : ∀{Ψ}{Ψ′} → Renameˢ Ψ Ψ′ → Renameˢ (suc Ψ) (suc Ψ′)
extˢ ρ Zˢ = Zˢ
extˢ ρ (Sˢ α) = Sˢ (ρ α)

singleSealEnv : ∀{Ψ} → Seal Ψ → Renameˢ (suc Ψ) Ψ
singleSealEnv α Zˢ = α
singleSealEnv α (Sˢ α′) = α′

renameˢⱽ : ∀{Δ}{Ψ}{Ψ′} → Renameˢ Ψ Ψ′ → TVar Δ Ψ → TVar Δ Ψ′
renameˢⱽ ρ (＇ X)   = ＇ X
renameˢⱽ ρ (｀ α)   = ｀ (ρ α)

renameˢ : ∀{Δ}{Ψ}{Ψ′} → Renameˢ Ψ Ψ′ → Ty Δ Ψ → Ty Δ Ψ′
renameˢ ρ (＇ X)   = ＇ X
renameˢ ρ (｀ α)   = ｀ (ρ α)
renameˢ ρ (‵ ι)   = ‵ ι
renameˢ ρ `★       = `★
renameˢ ρ (A ⇒ B)  = renameˢ ρ A ⇒ renameˢ ρ B
renameˢ ρ (`∀ A)   = `∀ (renameˢ ρ A)

⇑ˢⱽ : ∀{Δ}{Ψ} → TVar Δ Ψ → TVar Δ (suc Ψ)
⇑ˢⱽ = renameˢⱽ Sˢ

⇑ˢ : ∀{Δ}{Ψ} → Ty Δ Ψ → Ty Δ (suc Ψ)
⇑ˢ = renameˢ Sˢ

⤊ˢ : ∀{Δ}{Ψ} → Ctx Δ Ψ → Ctx Δ (suc Ψ)
⤊ˢ Γ = map ⇑ˢ Γ

renameStoreˢ : ∀{Ψ}{Ψ′} → Renameˢ Ψ Ψ′ → Store Ψ → Store Ψ′
renameStoreˢ ρ [] = []
renameStoreˢ ρ ((α , A) ∷ Σ) =
  (ρ α , renameˢ ρ A) ∷ renameStoreˢ ρ Σ

⟰ˢ : ∀{Ψ} → Store Ψ → Store (suc Ψ)
⟰ˢ = renameStoreˢ Sˢ

_[_]ˢ : ∀ {Δ}{Ψ} → Ty Δ (suc Ψ) → Seal Ψ → Ty Δ Ψ
A [ α ]ˢ = renameˢ (singleSealEnv α) A

------------------------------------------------------------------------
-- Lookup term variable in context
------------------------------------------------------------------------

infix 4 _∋_⦂_

data _∋_⦂_ : ∀{Δ}{Ψ} → Ctx Δ Ψ → Var → Ty Δ Ψ → Set where
  Z : ∀{Δ}{Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
      (A ∷ Γ) ∋ zero ⦂ A
      
  S : ∀{Δ}{Ψ}{Γ : Ctx Δ Ψ}{A B : Ty Δ Ψ}{x : Var} →
      Γ ∋ x ⦂ A →
      (B ∷ Γ) ∋ suc x ⦂ A

------------------------------------------------------------------------
-- Lookup seal in store
------------------------------------------------------------------------

infix 4 _∋ˢ_⦂_
data _∋ˢ_⦂_ : ∀{Ψ} → Store Ψ → Seal Ψ → Ty 0 Ψ → Set where
  Z∋ˢ : ∀{Ψ}{Σ : Store Ψ}{A B : Ty 0 Ψ}{α β : Seal Ψ}
       → α ≡ β
       → A ≡ B
       → ((β , B) ∷ Σ) ∋ˢ α ⦂ A
       
  S∋ˢ : ∀{Ψ}{Σ : Store Ψ}{α β : Seal Ψ}{A B : Ty 0 Ψ}
       → Σ ∋ˢ α ⦂ A
       → ((β , B) ∷ Σ) ∋ˢ α ⦂ A
