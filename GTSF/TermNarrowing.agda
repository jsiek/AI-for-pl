{-
  Term imprecision for the Nu syntax.

  This file mechanizes the term-imprecision relation from the cambridge22/23
  notes.  The paper presentation uses a combined environment for term variables
  and seal assumptions; here we split it into the store narrowing context from
  NarrowWiden and a term-variable context of coercions.

  Freshness side conditions from the paper are not reified here.  The paper's
  +/- cast notation is represented using NuTerms' single raw cast form and the
  coercion dual operator `-_`, with the corresponding coercion-equivalence
  premise made explicit.
-}

module TermNarrowing where

open import Data.List using (_∷_; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (∃-syntax)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition

variable
  Δ : TyCtx
  Σ : Store
  σ : StoreNrw
  γ : CtxNrw
  A A′ B : Ty
  p q r s t : Coercion
  M M′ N N′ L L′ V V′ : Term
  x : Var
  α αᵢ : TyVar

⇑ᵍ : CtxNrw → CtxNrw
⇑ᵍ = map ⇑ᶜ

infixl 7 _•_

_•_ : Term → TyVar → Term
L • α = ν (＇ α) L (id (＇ zero))

infix 4 _∣_∣_⊢_⊒_∶_

data _∣_∣_⊢_⊒_∶_
    : TyCtx → StoreNrw → CtxNrw → Term → Term → Coercion → Set₁ where

  extend : ∀ {M N′ p q A B α Σ}
    → ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ q ∶ B ⊒ A
    → Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ
        ⊢ M ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ
      ------------------------------------------------------
    → Δ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ M ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ

  split : ∀ {N N′ p q A α αᵢ Σ}
    → ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ q ∶ ★ ⊒ A
    → Δ ∣ (α ꞉ q) ∷ σ ∣ γ
        ⊢ N [ α ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ
      ----------------------------------------------------------
    → Δ ∣ (α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ ∣ γ
        ⊢ N [ αᵢ ]ᵀ ⊒ N′ [ α ]ᵀ ∶ p [ α ]ᶜ

  ⊒blame : ∀ {M p}
    → Δ ∣ σ ∣ γ ⊢ M ⊒ blame ∶ p

  x⊒x : ∀ {x p}
    → γ ∋ x ⦂ p
      -------------------------
    → Δ ∣ σ ∣ γ ⊢ ` x ⊒ ` x ∶ p

  ƛ⊒ƛ : ∀ {N N′ p q}
    → Δ ∣ σ ∣ ((- p) ∷ γ) ⊢ N ⊒ N′ ∶ q
      ---------------------------------
    → Δ ∣ σ ∣ γ ⊢ ƛ N ⊒ ƛ N′ ∶ p ↦ q

  ·⊒· : ∀ {L L′ M M′ p q}
    → Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ p ↦ q
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ - p
      -------------------------------
    → Δ ∣ σ ∣ γ ⊢ L · M ⊒ L′ · M′ ∶ q

  Λ⊒Λ : ∀ {V V′ p}
    → suc Δ ∣ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ V ⊒ V′ ∶ p
      ------------------------------------
    → Δ ∣ σ ∣ γ ⊢ Λ V ⊒ Λ V′ ∶ `∀ p

  ⊒Λ : ∀ {A N V′ p}
    → suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p
      --------------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ N ⊒ Λ V′ ∶ gen A p

  ⊒⟨ν⟩ : ∀ {A N V′ p s}
    → suc Δ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ ⇑ᵗᵐ N ⊒ V′ ⟨ s ⟩ ∶ p
      ----------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ N ⊒ V′ ⟨ gen A s ⟩ ∶ gen A p

  α⊒α : ∀ {L L′ p q α}
    → Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ `∀ p
      ------------------------------------------------
    → Δ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ L • α ⊒ L′ • α ∶ p [ α ]ᶜ

  ⊒α : ∀ {L L′ p A α}
    → Δ ∣ σ ∣ γ ⊢ L ⊒ L′ ∶ gen A p
      -----------------------------------------------
    → Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ ⊢ L ⊒ L′ • α ∶ p [ α ]ᶜ

  ν⊒ν : ∀ {A A′ N N′ p q Σ}
    → ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ A′
    → suc Δ ∣ (zero ꞉ ⇑ᶜ q) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ ⊢ N ⊒ N′ ∶ ⇑ᶜ p
      ------------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ ν A N (⇑ᶜ p) ⊒ ν A′ N′ (⇑ᶜ p) ∶ p

  ⊒ν : ∀ {A N N′ p}
    → suc Δ ∣ (zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ ⇑ᵗᵐ N ⊒ N′ ∶ ⇑ᶜ p
      ---------------------------------------
    → Δ ∣ σ ∣ γ ⊢ N ⊒ ν A N′ (⇑ᶜ p) ∶ p

  ν⊒ : ∀ {N N′ p}
    → suc Δ ∣ (⊒ zero ꞉=☆) ∷ ⇑ˢ σ ∣ ⇑ᵍ γ
        ⊢ N ⊒ ⇑ᵗᵐ N′ ∶ ⇑ᶜ p
      ----------------------------------
    → Δ ∣ σ ∣ γ ⊢ ν ★ N (⇑ᶜ p) ⊒ N′ ∶ p

  κ⊒κ : ∀ κ
      -------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ $ κ ⊒ $ κ ∶ id (constTy κ)

  ⊕⊒⊕ : ∀ {M M′ N N′}
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ id (‵ `ℕ)
    → Δ ∣ σ ∣ γ ⊢ N ⊒ N′ ∶ id (‵ `ℕ)
      -----------------------------------------------------
    → Δ ∣ σ ∣ γ ⊢ M ⊕[ addℕ ] N ⊒ M′ ⊕[ addℕ ] N′ ∶ id (‵ `ℕ)

  ⊒cast+ : ∀ {M M′ q r s A B}
    → Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r
      ----------------------------------
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ⟨ - s ⟩ ∶ q

  ⊒cast- : ∀ {M M′ q r s A B}
    → Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q
      ----------------------------------
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ⟨ s ⟩ ∶ r

  cast+⊒ : ∀ {M M′ p r t A B}
    → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p
      ----------------------------------
    → Δ ∣ σ ∣ γ ⊢ M ⟨ - t ⟩ ⊒ M′ ∶ r

  cast-⊒ : ∀ {M M′ p r t A B}
    → Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
    → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ r
      ----------------------------------
    → Δ ∣ σ ∣ γ ⊢ M ⟨ t ⟩ ⊒ M′ ∶ p
