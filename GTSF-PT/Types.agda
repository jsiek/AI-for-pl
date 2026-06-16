-- File Charter:
--   * Core syntax and primitive operations for types and type contexts.
--   * Primary exports are type variables, types, ground types, renaming,
--     substitution, and single-variable type substitution.
--   * Depends only on standard-library data and equality utilities.

module Types where

-- Note to self:
--   * Put new lemmas/proofs in the most specific module, not here, unless they are
--     definitional properties of these core operations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong)

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

tyVarToFin : ∀ {Δ} → TyVar Δ → Fin Δ
tyVarToFin Zᵗ = zero
tyVarToFin (Sᵗ X) = suc (tyVarToFin X)

data Base : Set where
  `ℕ  : Base
  `𝔹  : Base

infixr 7 _⇒_
infix  6 `∀

data Ty : TyCtx → Set where
  ＇_  : ∀{Δ} (X : TyVar Δ) → Ty Δ
  ‵_   : ∀{Δ} → (ι : Base) → Ty Δ
  `★   : ∀{Δ} → Ty Δ
  _⇒_  : ∀{Δ} → Ty Δ → Ty Δ → Ty Δ
  `∀   : ∀{Δ} → Ty (suc Δ) → Ty Δ

data Cross : ∀{Δ} → Ty Δ → Set where
  ＇_ : ∀{Δ} (X : TyVar Δ) → Cross{Δ} (＇ X)
  ‵_ : ∀{Δ} → (ι : Base) → Cross{Δ} (‵ ι)
  _⇒_ : ∀{Δ} → (A : Ty Δ) → (B : Ty Δ) → Cross (A ⇒ B)
  `∀  : ∀{Δ} → (A : Ty (suc Δ)) → Cross (`∀ A)

data Ground : ∀{Δ} → Ty Δ → Set where
  ‵_ : ∀{Δ} → (ι : Base) → Ground{Δ} (‵ ι)
  ★⇒★ : ∀{Δ} → Ground{Δ} (`★ ⇒ `★)

infix 4 _≟Base_
_≟Base_ : (ι ι′ : Base) → Dec (ι ≡ ι′)
`ℕ ≟Base `ℕ = yes refl
`ℕ ≟Base `𝔹 = no (λ ())
`𝔹 ≟Base `ℕ = no (λ ())
`𝔹 ≟Base `𝔹 = yes refl

infix 4 _≟Ground_
_≟Ground_ :
  ∀{Δ}{G H : Ty Δ} →
  Ground G →
  Ground H →
  Dec (G ≡ H)
(‵ ι) ≟Ground (‵ ι′) with ι ≟Base ι′
... | yes eq = yes (cong ‵_ eq)
... | no neq = no (λ { refl → neq refl })
(‵ ι) ≟Ground ★⇒★ = no (λ ())
★⇒★ ≟Ground (‵ ι) = no (λ ())
★⇒★ ≟Ground ★⇒★ = yes refl

Ctx : TyCtx → Set
Ctx Δ = List (Ty Δ)

------------------------------------------------------------------------
-- Type-variable substitution (de Bruijn X)
------------------------------------------------------------------------

Renameᵗ : TyCtx → TyCtx → Set
Renameᵗ Δ Δ′ = TyVar Δ → TyVar Δ′

Substᵗ : TyCtx → TyCtx → Set
Substᵗ Δ Δ′ = TyVar Δ → Ty Δ′

extᵗ : ∀{Δ}{Δ′} → Renameᵗ Δ Δ′ → Renameᵗ (suc Δ) (suc Δ′)
extᵗ ρ Zᵗ = Zᵗ
extᵗ ρ (Sᵗ X) = Sᵗ (ρ X)

renameᵗ : ∀ {Δ}{Δ′} → Renameᵗ Δ Δ′ → Ty Δ → Ty Δ′
renameᵗ ρ (＇ X) = ＇ (ρ X)
renameᵗ ρ (‵ ι) = ‵ ι
renameᵗ ρ `★ = `★
renameᵗ ρ (A ⇒ B) = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A) = `∀ (renameᵗ (extᵗ ρ) A)

extsᵗ : ∀ {Δ}{Δ′} → Substᵗ Δ Δ′ → Substᵗ (suc Δ) (suc Δ′)
extsᵗ σ Zᵗ = ＇ Zᵗ
extsᵗ σ (Sᵗ X) = renameᵗ Sᵗ (σ X)

substᵗ : ∀ {Δ}{Δ′} → Substᵗ Δ Δ′ → Ty Δ → Ty Δ′
substᵗ σ (＇ X) = σ X
substᵗ σ (‵ ι) = ‵ ι
substᵗ σ `★ = `★
substᵗ σ (A ⇒ B) = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A) = `∀ (substᵗ (extsᵗ σ) A)

singleTyEnv : ∀ {Δ} → Ty Δ → Substᵗ (suc Δ) Δ
singleTyEnv B Zᵗ    = B
singleTyEnv B (Sᵗ X) = ＇ X

infixl 8 _[_]ᵗ
_[_]ᵗ : ∀ {Δ} → Ty (suc Δ) → Ty Δ → Ty Δ
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

------------------------------------------------------------------------
-- Lift closed store types (Ty 0) into an arbitrary Δ
------------------------------------------------------------------------

lift0ᵗ : ∀{Δ} → Renameᵗ 0 Δ
lift0ᵗ ()

wkTy0 : ∀{Δ} → Ty 0 → Ty Δ
wkTy0 = renameᵗ lift0ᵗ

wkTy : ∀ {Δ} → Ty Δ → Ty (suc Δ)
wkTy = renameᵗ Sᵗ

------------------------------------------------------------------------
-- Lookup term variable in context
------------------------------------------------------------------------

infix 4 _∋_⦂_

data _∋_⦂_ : ∀{Δ} → Ctx Δ → Var → Ty Δ → Set where
  Z : ∀{Δ}{Γ : Ctx Δ}{A : Ty Δ} →
      (A ∷ Γ) ∋ zero ⦂ A

  S : ∀{Δ}{Γ : Ctx Δ}{A B : Ty Δ}{x : Var} →
      Γ ∋ x ⦂ A →
      (B ∷ Γ) ∋ suc x ⦂ A

----------------------------------------------------------------------
-- base type interpretation
----------------------------------------------------------------------

base-type : Base → Set
base-type `ℕ = ℕ
base-type `𝔹 = Bool
