module Imprecision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)

open import Types

Label : Set
Label = ℕ

------------------------------------------------------------------------
-- Intrinsically typed polymorphic imprecision witnesses
------------------------------------------------------------------------

infixr 7 _↦_
infixl 6 _；_
infixr 6 _⨟_
infix 5 _⊢_⊑_
infix 5 _⊢_⊑ᵃ_

mutual
  data _⊢_⊑ᵃ_ {Δ}{Ψ} (Σ : Store Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
    tag : ∀{G}
      → Ground G
      → Label
      → Σ ⊢ G ⊑ᵃ `★

    `⊥ : ∀{A B}
      → Label
      → Σ ⊢ A ⊑ᵃ B

    seal : ∀{α}{A}
      → Σ ∋ˢ α ⦂ A
      → Σ ⊢ ｀ α ⊑ᵃ wkTy0 A

    _↦_ : ∀{A A′ B B′}
      → Σ ⊢ A′ ⊑ A
      → Σ ⊢ B ⊑ B′
      → Σ ⊢ (A ⇒ B) ⊑ᵃ (A′ ⇒ B′)

    ∀ᵖ : ∀{A B : Ty (suc Δ) Ψ}
      → Σ ⊢ A ⊑ B
      → Σ ⊢ (`∀ A) ⊑ᵃ (`∀ B)

    ν_ : ∀{A : Ty (suc Δ) Ψ}{B : Ty Δ Ψ}
      → ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)
      → Σ ⊢ (`∀ A) ⊑ᵃ B

  data _⊢_⊑_ {Δ}{Ψ} (Σ : Store Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
    id : ∀{A}
      → Σ ⊢ A ⊑ A

    _；_ : ∀{A B C}
      → Σ ⊢ A ⊑ B
      → Σ ⊢ B ⊑ᵃ C
      → Σ ⊢ A ⊑ C

_⨟_ : ∀{Δ}{Ψ}{Σ : Store Ψ}{A B C : Ty Δ Ψ}
  → Σ ⊢ A ⊑ B
  → Σ ⊢ B ⊑ C
  → Σ ⊢ A ⊑ C
p ⨟ id = p
p ⨟ (q ； a) = (p ⨟ q) ； a

castᵖ :
  ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}
    {A A′ B B′ : Ty Δ Ψ} →
  Σ ≡ Σ′ →
  A ≡ A′ →
  B ≡ B′ →
  Σ ⊢ A ⊑ B →
  Σ′ ⊢ A′ ⊑ B′
castᵖ refl refl refl p = p
