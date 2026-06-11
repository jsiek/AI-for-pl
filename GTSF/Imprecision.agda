module Imprecision where

-- File Charter:
--   * Imprecision on types

open import Types

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Product using
  (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (cong)

data ImpAssm : Set where
  _ˣ⊑★ : TyVar → ImpAssm
  _ˣ⊑ˣ_ : TyVar → TyVar → ImpAssm

ImpCtx : Set
ImpCtx = List ImpAssm

⇑ᵢₐ : ImpAssm → ImpAssm
⇑ᵢₐ (X ˣ⊑★) = suc X ˣ⊑★
⇑ᵢₐ (X ˣ⊑ˣ Y) = suc X ˣ⊑ˣ suc Y

⇑ᴸᵢₐ : ImpAssm → ImpAssm
⇑ᴸᵢₐ (X ˣ⊑★) = suc X ˣ⊑★
⇑ᴸᵢₐ (X ˣ⊑ˣ Y) = suc X ˣ⊑ˣ Y

⇑ᵢ : ImpCtx → ImpCtx
⇑ᵢ [] = []
⇑ᵢ (m ∷ Φ) = ⇑ᵢₐ m ∷ ⇑ᵢ Φ

⇑ᴸᵢ : ImpCtx → ImpCtx
⇑ᴸᵢ [] = []
⇑ᴸᵢ (m ∷ Φ) = ⇑ᴸᵢₐ m ∷ ⇑ᴸᵢ Φ

------------------------------------------------------------------------
-- Type Imprecision
------------------------------------------------------------------------

infix 4 _⊢_⊑_
data _⊢_⊑_ (Φ : ImpCtx) : Ty → Ty → Set where
  id★ :
    -------------
    Φ ⊢ ★ ⊑ ★

  idˣ : ∀ {X Y}
    → (X ˣ⊑ˣ Y) ∈ Φ
    ---------------------
    → Φ ⊢ ＇ X ⊑ ＇ Y
    
  idι : ∀ {ι}
    -------------------
    → Φ ⊢ ‵ ι ⊑ ‵ ι

  _↦_ : ∀ {A A′ B B′} →
    Φ ⊢ A ⊑ A′ →
    Φ ⊢ B ⊑ B′ →
    ---------------------------
    Φ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ∀ⁱ_ : ∀ {A B}
    → {occA : occurs zero A ≡ true}
    → {occB : occurs zero B ≡ true}
    → (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ ⊢ A ⊑ B
    ----------------------------
    → Φ ⊢ (`∀ A) ⊑ (`∀ B)

  tag_ : ∀ (ι : Base)
    → Φ ⊢ ‵ ι ⊑ ★

  tag_⇒_ : ∀ {A₁ A₂}
    → Φ ⊢ A₁ ⊑ ★
    → Φ ⊢ A₂ ⊑ ★
    ---------------------
    → Φ ⊢ A₁ ⇒ A₂ ⊑ ★

  tagˣ_ : ∀ {X}
    → X ˣ⊑★ ∈ Φ
    ------------------
    → Φ ⊢ ＇ X ⊑ ★

  ν : ∀ {A B}
    → occurs zero A ≡ true
    → (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ ⊢ A ⊑ B
    -------------------------
    → Φ ⊢ (`∀ A) ⊑ B


------------------------------------------------------------------------
-- Consistency is common lower bound
------------------------------------------------------------------------

idᵢ : TyCtx → ImpCtx
idᵢ zero = []
idᵢ (suc Δ) = (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (idᵢ Δ)

infix 4 _⊢_~_
_⊢_~_ : TyCtx → Ty → Ty → Set
Δ ⊢ A ~ B = ∃[ C ] idᵢ Δ ⊢ C ⊑ A × idᵢ Δ ⊢ C ⊑ B
