module PolyBlame where

open import Data.List using (_∷_; map)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Product using (_,_)
open import Types
open import Imprecision

------------------------------------------------------------------------
-- Constants and primitive operators (κ and ⊕)
------------------------------------------------------------------------

data Const : Set where
  κℕ : ℕ → Const

constTy : ∀{Δ}{Ψ} → Const → Ty Δ Ψ
constTy (κℕ n) = ‵ `ℕ

data Prim : Set where
  addℕ : Prim

primTy : ∀{Δ}{Ψ} → Prim → Ty Δ Ψ
primTy addℕ = ‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ

data δ : Prim → Const → Const → Const → Set where
  δ-add : {m n : ℕ} →
          δ addℕ (κℕ m) (κℕ n) (κℕ (m + n))

------------------------------------------------------------------------
-- Intrinsic terms
------------------------------------------------------------------------

⤊ᵗ : ∀{Δ}{Ψ} → Ctx Δ Ψ → Ctx (suc Δ) Ψ
⤊ᵗ Γ = map (renameᵗ Sᵗ) Γ

data Cast : (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Ψ)
          → Ty Δ Ψ → Ty Δ Ψ → Set where
  up_   : ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
          Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
          Cast Δ Ψ Σ A B

  down_ : ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
          Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
          Cast Δ Ψ Σ B A

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _·α_[_]
infix  5 ν:=_∙_
infixl 6 _⊕[_]_
infix  8 _at_
infix  9 `_
infix  4 _∣_∣_∣_⊢_

data _∣_∣_∣_⊢_ (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Ψ) (Γ : Ctx Δ Ψ) : Ty Δ Ψ → Set where
  `_        : ∀{A : Ty Δ Ψ}{x : Var} →
              Γ ∋ x ⦂ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

  ƛ_⇒_      : ∀{B : Ty Δ Ψ} →
              (A : Ty Δ Ψ) →
              Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ B →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)

  _·_       : ∀{A B : Ty Δ Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  Λ_        : ∀{A : Ty (suc Δ) Ψ} →
              (suc Δ) ∣ Ψ ∣ Σ ∣ (⤊ᵗ Γ) ⊢ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)

  _·α_[_]   : ∀{A : Ty (suc Δ) Ψ}{C : Ty 0 Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A) →
              (α : Seal Ψ) →
              Σ ∋ˢ α ⦂ C →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A [ ｀ α ]ᵗ)

  ν:=_∙_    : ∀{B : Ty Δ Ψ} →
              (A : Ty 0 Ψ) →
              Δ ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ (⇑ˢ B) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  $         :
              (κ : Const) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (constTy κ)

  _⊕[_]_    :
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ) →
              (op : Prim) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)

  _at_      : ∀{A B : Ty Δ Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
              Cast Δ Ψ Σ A B →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  blame     : ∀{A : Ty Δ Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A
