module Consistency where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
  renaming (subst to substEq)

open import Types
open import TypeSubst
open import TypePrecision

------------------------------------------------------------------------
-- Type Precision 
------------------------------------------------------------------------

infix 5 _⊢_~_

mutual
  data _⊢_~_ {Δ}{Ψ} (Σ : Store Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
  
    X~X : ∀{X : TyVar Δ} → Σ ⊢ ＇ X ~ ＇ X
    
    α~α : ∀{α : Seal Ψ} → Σ ⊢ ｀ α ~ ｀ α
    
    ι~ι : ∀{ι : Base} → Σ ⊢ ‵ ι ~ ‵ ι

    ★~★ : Σ ⊢ `★ ~ `★
      
    ★~G : ∀{G}
      → Ground G
      → Σ ⊢ `★ ~ G

    G~★ : ∀{G}
      → Ground G
      → Σ ⊢ G ~ `★

    ★~⇒ : ∀{A B}
      → Σ ⊢ A ~ `★
      → Σ ⊢ `★ ~ B
      → Σ ⊢ `★ ~ (A ⇒ B)

    ⇒~★ : ∀{A B}
      → Σ ⊢ `★ ~ A
      → Σ ⊢ B ~ `★
      → Σ ⊢ (A ⇒ B) ~ `★

    A~α : ∀{α}{A}
      → Σ ∋ˢ α ⦂ A
      → Σ ⊢ wkTy0 A ~ ｀ α

    α~A : ∀{α}{A}
      → Σ ∋ˢ α ⦂ A
      → Σ ⊢ ｀ α ~ wkTy0 A

    ↦~↦ : ∀{A A′ B B′}
      → Σ ⊢ A′ ~ A
      → Σ ⊢ B ~ B′
      → Σ ⊢ (A ⇒ B) ~ (A′ ⇒ B′)

    ∀~∀ : ∀{A B : Ty (suc Δ) Ψ}
      → Σ ⊢ A ~ B
      → Σ ⊢ (`∀ A) ~ (`∀ B)

    ∀~ : ∀{A : Ty (suc Δ) Ψ}{B : Ty Δ Ψ}
      → ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ~ (⇑ˢ B)
      → Σ ⊢ (`∀ A) ~ B

    ~∀ : ∀{A : Ty Δ Ψ}{B : Ty (suc Δ) Ψ}
      → ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ (⇑ˢ A) ~ ((⇑ˢ B) [ ｀ Zˢ ]ᵗ)
      → Σ ⊢ A ~ (`∀ B)

