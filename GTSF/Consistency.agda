module Consistency where

-- File Charter:
--   * Definition of the GTSF type-consistency relation `~`.
--   * Introduce the judgment only; transport/proof lemmas live in
--     `ConsistencyProperties.agda`.
--   * No coercion synthesis here.

open import Data.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
  renaming (subst to substEq)

open import Types

------------------------------------------------------------------------
-- Consistency context and lookup
------------------------------------------------------------------------

-- Assumptions
data CAssm : Set where
  _~ᶜ★ : TyVar → CAssm
  ★~ᶜ_ : TyVar → CAssm
  _~ᶜ_ : TyVar → TyVar → CAssm

CCtx : Set
CCtx = List CAssm

⇑ₐ : CAssm → CAssm
⇑ₐ (X ~ᶜ★) = suc X ~ᶜ★
⇑ₐ (★~ᶜ Y) = ★~ᶜ suc Y
⇑ₐ (X ~ᶜ Y) = suc X ~ᶜ suc Y

⇑ᴸₐ : CAssm → CAssm
⇑ᴸₐ (X ~ᶜ★) = suc X ~ᶜ★
⇑ᴸₐ (★~ᶜ Y) = ★~ᶜ Y
⇑ᴸₐ (X ~ᶜ Y) = suc X ~ᶜ Y

⇑ᴿₐ : CAssm → CAssm
⇑ᴿₐ (X ~ᶜ★) = X ~ᶜ★
⇑ᴿₐ (★~ᶜ Y) = ★~ᶜ suc Y
⇑ᴿₐ (X ~ᶜ Y) = X ~ᶜ suc Y

⇑ : List CAssm → List CAssm
⇑ = λ Γ → map ⇑ₐ Γ
⇑ᴸ = λ Γ → map ⇑ᴸₐ Γ
⇑ᴿ = λ Γ → map ⇑ᴿₐ Γ

------------------------------------------------------------------------
-- Type Consistency
------------------------------------------------------------------------

infix 4 _⊢_~_

data _⊢_~_ (Γ : CCtx) : Ty → Ty → Set where

  ★-~-★ : Γ ⊢ ★ ~ ★

  X-~-Y : ∀ {X Y}
    → (X ~ᶜ Y) ∈ Γ
    ---------------
    → Γ ⊢ ＇ X ~ ＇ Y

  ι-~-ι : ∀ {ι} →
    Γ ⊢ ‵ ι ~ ‵ ι

  ⇒-~-⇒ : ∀ {A A′ B B′} →
    Γ ⊢ A ~ A′ →
    Γ ⊢ B ~ B′ →
    -----------------------
    Γ ⊢ (A ⇒ B) ~ (A′ ⇒ B′)

  ∀-~-∀ : ∀ {A B} 
    → (0 ~ᶜ 0) ∷ (⇑ Γ) ⊢ A ~ B
    ------------------------
    → Γ ⊢ (`∀ A) ~ (`∀ B)

  ι-~-★ : ∀ {ι}
    → Γ ⊢ ‵ ι ~ ★

  ⇒-~-★ : ∀ {A₁ A₂}
    → Γ ⊢ A₁ ~ ★
    → Γ ⊢ A₂ ~ ★
    -----------------
    → Γ ⊢ A₁ ⇒ A₂ ~ ★

  νX-~-★ : ∀ {X}
    → (X ~ᶜ★) ∈ Γ
    ---------------
    → Γ ⊢ ＇ X ~ ★

  ★-~-ι : ∀ {ι} →
    Γ ⊢ ★ ~ ‵ ι
    
  ★-~-⇒ : ∀ {B₁ B₂} →
    Γ ⊢ ★ ~ B₁ →
    Γ ⊢ ★ ~ B₂ →
    ---------------
    Γ ⊢ ★ ~ B₁ ⇒ B₂

  ★-~-νX : ∀ {X}
    → (★~ᶜ X) ∈ Γ
    ---------------
    → Γ ⊢ ★ ~ ＇ X

  ∀-~-B : ∀ {A B}
    → occurs zero A ≡ true
    → (0 ~ᶜ★) ∷ ⇑ᴸ Γ ⊢ A ~ B
    ------------------------
    → Γ ⊢ (`∀ A) ~ B

  A-~-∀ : ∀ {A B}
    → occurs zero B ≡ true
    → (★~ᶜ 0) ∷ ⇑ᴿ Γ ⊢ A ~ B
    ------------------------
    → Γ ⊢ A ~ (`∀ B)


