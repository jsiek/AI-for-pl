module TypePrecision where

-- File Charter:
--   * Definition of the type-precision judgments (`⊑ᵃ`, `⊑`) and their composition.
--   * Introduce the relations only; reusable transport properties belong in
--     `TypePrecisionProperties.agda`.
--   * No consistency, coercion synthesis, or store-specific metatheory beyond what the
--     judgment constructors require.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
  renaming (subst to substEq)

open import Types
open import TypeSubst

------------------------------------------------------------------------
-- Type Precision 
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
      → Σ ⊢ `★ ⊑ᵃ G

    seal : ∀{α}{A}
      → Σ ∋ˢ α ⦂ A
      → Σ ⊢ wkTy0 A ⊑ᵃ ｀ α

    _↦_ : ∀{A A′ B B′}
      → Σ ⊢ A ⊑ A′
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

infix 8 〔_〕
pattern 〔_〕 p = id ； p
