module Imprecision where

-- File Charter:
--   * Defines type imprecision assumptions and the raw type relation.
--   * Provides matched, source-only, and target-only shifts of assumption
--     contexts for polymorphic runtime allocation.
--   * Defines the crossed context for two logically permuted allocations.

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

⇑ᴿᵢₐ : ImpAssm → ImpAssm
⇑ᴿᵢₐ (X ˣ⊑★) = X ˣ⊑★
⇑ᴿᵢₐ (X ˣ⊑ˣ Y) = X ˣ⊑ˣ suc Y

⇑ᵢ : ImpCtx → ImpCtx
⇑ᵢ [] = []
⇑ᵢ (m ∷ Φ) = ⇑ᵢₐ m ∷ ⇑ᵢ Φ

⇑ᴸᵢ : ImpCtx → ImpCtx
⇑ᴸᵢ [] = []
⇑ᴸᵢ (m ∷ Φ) = ⇑ᴸᵢₐ m ∷ ⇑ᴸᵢ Φ

⇑ᴿᵢ : ImpCtx → ImpCtx
⇑ᴿᵢ [] = []
⇑ᴿᵢ (m ∷ Φ) = ⇑ᴿᵢₐ m ∷ ⇑ᴿᵢ Φ

swapRight∀∀ᵢ : ImpCtx → ImpCtx
swapRight∀∀ᵢ Φ =
  (zero ˣ⊑ˣ suc zero) ∷
  (suc zero ˣ⊑ˣ zero) ∷
  ⇑ᵢ (⇑ᵢ Φ)

------------------------------------------------------------------------
-- Type Imprecision
------------------------------------------------------------------------

-- A source body generalized by `ν` cannot be a bare type variable.  Together
-- with the occurrence premise on `ν`, this leaves exactly function and
-- universal bodies: base types and `★` cannot contain the fresh variable.
-- The separation keeps the type-level side condition independent of the
-- operational `GenSafe` coercion category.
data NonVar : Ty → Set where
  nonvar-base : ∀ {ι} → NonVar (‵ ι)
  nonvar-star : NonVar ★
  nonvar-fun : ∀ {A B} → NonVar (A ⇒ B)
  nonvar-all : ∀ {A} → NonVar (`∀ A)

nonVar-unique :
  ∀ {A} →
  (p q : NonVar A) →
  p ≡ q
nonVar-unique nonvar-base nonvar-base = refl
nonVar-unique nonvar-star nonvar-star = refl
nonVar-unique nonvar-fun nonvar-fun = refl
nonVar-unique nonvar-all nonvar-all = refl

instance
  nonVar-base-instance : ∀ {ι} → NonVar (‵ ι)
  nonVar-base-instance = nonvar-base

  nonVar-star-instance : NonVar ★
  nonVar-star-instance = nonvar-star

  nonVar-fun-instance : ∀ {A B} → NonVar (A ⇒ B)
  nonVar-fun-instance = nonvar-fun

  nonVar-all-instance : ∀ {A} → NonVar (`∀ A)
  nonVar-all-instance = nonvar-all

renameNonVar :
  ∀ {A} →
  (ρ : Renameᵗ) →
  NonVar A →
  NonVar (renameᵗ ρ A)
renameNonVar ρ nonvar-base = nonvar-base
renameNonVar ρ nonvar-star = nonvar-star
renameNonVar ρ nonvar-fun = nonvar-fun
renameNonVar ρ nonvar-all = nonvar-all

substNonVar :
  ∀ {A} →
  (cons : Substᵗ) →
  NonVar A →
  NonVar (substᵗ cons A)
substNonVar cons nonvar-base = nonvar-base
substNonVar cons nonvar-star = nonvar-star
substNonVar cons nonvar-fun = nonvar-fun
substNonVar cons nonvar-all = nonvar-all

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
    → (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ ⊢ A ⊑ B
    ----------------------------
    → Φ ⊢ (`∀ A) ⊑ (`∀ B)

  tag_ : ∀ (ι : Base)
    → Φ ⊢ ‵ ι ⊑ ★

  tag_⇛_ : ∀ {A₁ A₂}
    → Φ ⊢ A₁ ⊑ ★
    → Φ ⊢ A₂ ⊑ ★
    ---------------------
    → Φ ⊢ A₁ ⇒ A₂ ⊑ ★

  tagˣ_ : ∀ {X}
    → X ˣ⊑★ ∈ Φ                -- This X is an α
    ------------------
    → Φ ⊢ ＇ X ⊑ ★

  ν : ∀ {A B}
    → NonVar A
    → occurs zero A ≡ true      -- Phil: keep this, need for unique derivations
    → (0 ˣ⊑★) ∷ ⇑ᵢ Φ ⊢ A ⊑ ⇑ᵗ B
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
