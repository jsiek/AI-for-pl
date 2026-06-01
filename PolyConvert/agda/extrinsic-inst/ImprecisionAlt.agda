module ImprecisionAlt where

-- File Charter:
--   * Imprecision on types (alternative design to the one in Imprecision.agda)

open import Types

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

data ImpAssm : Set where
  _ˣ⊑★ : TyVar → ImpAssm
  _ˣ⊑ˣ_ : TyVar → TyVar → ImpAssm

ImpCtx : Set
ImpCtx = List ImpAssm

infix 4 _∣_⊢_⊑_
data _∣_⊢_⊑_ (Ψ : SealCtx) (Φ : ImpCtx) : Ty → Ty → Set where
  id★ :
    -------------
    Ψ ∣ Φ ⊢ ★ ⊑ ★

  idˣ : ∀ {X Y}
    → (X ˣ⊑ˣ Y) ∈ Φ
    ---------------------
    → Ψ ∣ Φ ⊢ ＇ X ⊑ ＇ Y
    
  idι : ∀ {ι}
    -------------------
    → Ψ ∣ Φ ⊢ ‵ ι ⊑ ‵ ι

  idα : ∀ {α}
    → WfTy (length Φ) Ψ (｀ α)
    --------------------------
    → Ψ ∣ Φ ⊢ ｀ α ⊑ ｀ α

  _↦_ : ∀ {A A′ B B′} →
    Ψ ∣ Φ ⊢ A ⊑ A′ →
    Ψ ∣ Φ ⊢ B ⊑ B′ →
    ---------------------------
    Ψ ∣ Φ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ∀ⁱ_ : ∀ {A B}
    → Ψ ∣ (0 ˣ⊑ˣ 0) ∷ Φ ⊢ A ⊑ B
    ----------------------------
    → Ψ ∣ Φ ⊢ (`∀ A) ⊑ (`∀ B)

  tag_ : ∀ (ι : Base)
    → Ψ ∣ Φ ⊢ ‵ ι ⊑ ★

  tag_⇒_ : ∀ {A₁ A₂}
    → Ψ ∣ Φ ⊢ A₁ ⊑ ★
    → Ψ ∣ Φ ⊢ A₂ ⊑ ★
    ---------------------
    → Ψ ∣ Φ ⊢ A₁ ⇒ A₂ ⊑ ★

  tagˣ_ : ∀ {X}
    → X ˣ⊑★ ∈ Φ
    ------------------
    → Ψ ∣ Φ ⊢ ＇ X ⊑ ★

  ν : ∀ {A B}
    → occurs zero A ≡ true
    → Ψ ∣ (0 ˣ⊑★) ∷ Φ ⊢ A ⊑ B
    -------------------------
    → Ψ ∣ Φ ⊢ (`∀ A) ⊑ B

