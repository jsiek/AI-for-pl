module GradualTerms where

-- File Charter:
--   * Source-language gradual term syntax and typing for GTSF.
--   * This layer uses the type consistency relation from `Imprecision`.
--   * These terms are intended to compile to the intermediate language in
--     `NuTerms.agda`; no target coercions appear in this source syntax.
--   * Application and primitive-operation nodes carry source labels used by
--     compilation when they generate casts.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision using (_⊢_~_)
open import Primitives using (Const; Prim; constTy)

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·[_]_
infixl 7 _`[_]
infixl 6 _⊕[_at_]_
infix  9 `_

data GTerm : Set where
  `_      : Var → GTerm
  ƛ_⇒_    : Ty → GTerm → GTerm
  _·[_]_  : GTerm → Label → GTerm → GTerm
  Λ_      : GTerm → GTerm
  _`[_]   : GTerm → Ty → GTerm
  $       : Const → GTerm
  _⊕[_at_]_ : GTerm → Prim → Label → GTerm → GTerm

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : GTerm → Set where
  ƛ_⇒_ :
    (A : Ty) (N : GTerm) →
    Value (ƛ A ⇒ N)

  $ :
    (κ : Const) →
    Value ($ κ)

  Λ_ :
    (N : GTerm) →
    Value (Λ N)

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix  4 _∣_⊢_⦂_

data _∣_⊢_⦂_ (Δ : TyCtx) (Γ : Ctx) : GTerm → Ty → Set₁ where

  ⊢` : ∀ {x A}
     → Γ ∋ x ⦂ A
     → Δ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {M A B}
     → WfTy Δ A
     → Δ ∣ (A ∷ Γ) ⊢ M ⦂ B
     → Δ ∣ Γ ⊢ (ƛ A ⇒ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {L M A A′ B ℓ}
     → Δ ∣ Γ ⊢ L ⦂ (A ⇒ B)
     → Δ ∣ Γ ⊢ M ⦂ A′
     → Δ ⊢ A ~ A′
     → Δ ∣ Γ ⊢ (L ·[ ℓ ] M) ⦂ B

  ⊢·★ : ∀ {L M A′ ℓ}
     → Δ ∣ Γ ⊢ L ⦂ ★
     → Δ ∣ Γ ⊢ M ⦂ A′
     → Δ ⊢ A′ ~ ★
     → Δ ∣ Γ ⊢ (L ·[ ℓ ] M) ⦂ ★

  ⊢Λ : ∀ {M A} {occ : occurs zero A ≡ true}
     → Value M
     → (suc Δ) ∣ (⤊ᵗ Γ) ⊢ M ⦂ A
     → Δ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {M B A}
     → Δ ∣ Γ ⊢ M ⦂ (`∀ B)
     → WfTy (suc Δ) B
     → WfTy Δ A
     → Δ ∣ Γ ⊢ (M `[ A ]) ⦂ B [ A ]ᵗ

  ⊢$ : ∀ (κ : Const)
     → Δ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M A B ℓ}
     → Δ ∣ Γ ⊢ L ⦂ A
     → Δ ⊢ A ~ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Γ ⊢ M ⦂ B
     → Δ ⊢ B ~ (‵ `ℕ)
     → Δ ∣ Γ ⊢ (L ⊕[ op at ℓ ] M) ⦂ (‵ `ℕ)
