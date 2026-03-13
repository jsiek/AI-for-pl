module PolyCoercions where

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Bool using (Bool)
open import PolyTypes public

------------------------------------------------------------------------
-- Coercions (Fig. 1)
------------------------------------------------------------------------

infixr 7 _↦_
infixr 7 ∀ᶜ_
infixr 6 _⨟_
infixr 6 _`?_
infixr 6 _!

data Coercion : Set where
  idᶜ : Ty → Coercion
  _!  : Ty → Coercion
  _`?_ : Ty → Label → Coercion
  _⁻ : Name → Coercion
  _⁺ : Name → Coercion
  _↦_ : Coercion → Coercion → Coercion
  ∀ᶜ_ : Coercion → Coercion
  _⨟_ : Coercion → Coercion → Coercion
  ⊥ᶜ_⦂_⇨_ : Label → Ty → Ty → Coercion

------------------------------------------------------------------------
-- Coercion typing (Fig. 2)
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_⇨_

data _∣_⊢_⦂_⇨_ (Σ : Store) (Δ : TyCtx) : Coercion → Ty → Ty → Set where
  ⊢idᶜ : ∀ {A}
    → WfTy Δ Σ A
    → Σ ∣ Δ ⊢ idᶜ A ⦂ A ⇨ A

  ⊢! : ∀ {G}
    → WfTy Δ Σ G
    → Ground G
    → Σ ∣ Δ ⊢ G ! ⦂ G ⇨ `★

  ⊢? : ∀ {G p}
    → WfTy Δ Σ G
    → Ground G
    → Σ ∣ Δ ⊢ G `? p ⦂ `★ ⇨ G

  ⊢↦ : ∀ {A A′ B B′ c d}
    → Σ ∣ Δ ⊢ c ⦂ A′ ⇨ A
    → Σ ∣ Δ ⊢ d ⦂ B ⇨ B′
    → Σ ∣ Δ ⊢ c ↦ d ⦂ (A ⇒ B) ⇨ (A′ ⇒ B′)

  ⊢⨟ : ∀ {A B C c d}
    → Σ ∣ Δ ⊢ c ⦂ A ⇨ B
    → Σ ∣ Δ ⊢ d ⦂ B ⇨ C
    → Σ ∣ Δ ⊢ c ⨟ d ⦂ A ⇨ C

  ⊢conceal : ∀ {U A}
    → Σ ∋ᵁ U ⦂ A
    → Σ ∣ Δ ⊢ U ⁻ ⦂ A ⇨ `U U

  ⊢reveal : ∀ {U A}
    → Σ ∋ᵁ U ⦂ A
    → Σ ∣ Δ ⊢ U ⁺ ⦂ `U U ⇨ A

  ⊢∀ᶜ : ∀ {A B c}
    → renameΣ suc Σ ∣ suc Δ ⊢ c ⦂ A ⇨ B
    → Σ ∣ Δ ⊢ ∀ᶜ c ⦂ `∀ A ⇨ `∀ B

  ⊢⊥ : ∀ {p A B}
    → WfTy Δ Σ A
    → WfTy Δ Σ B
    → Σ ∣ Δ ⊢ (⊥ᶜ p ⦂ A ⇨ B) ⦂ A ⇨ B
