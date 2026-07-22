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

-- A source body generalized by `ν` must expose a value-preserving coercion
-- shape.  Functions do so directly; an outer universal gives an inert
-- all-coercion, while any nested source-only generalization checks its own
-- body.  In particular, a bare bound variable is excluded because
-- compiling it against `★` would put its active projection directly beneath
-- `gen`.
data GenSafeSource : Ty → Set where
  source-fun : ∀ {A B} → GenSafeSource (A ⇒ B)
  source-all : ∀ {A} → GenSafeSource (`∀ A)

genSafeSource-unique :
  ∀ {A} →
  (p q : GenSafeSource A) →
  p ≡ q
genSafeSource-unique source-fun source-fun = refl
genSafeSource-unique source-all source-all = refl

instance
  genSafeSource-fun : ∀ {A B} → GenSafeSource (A ⇒ B)
  genSafeSource-fun = source-fun

  genSafeSource-all : ∀ {A} → GenSafeSource (`∀ A)
  genSafeSource-all = source-all

renameGenSafeSource :
  ∀ {A} →
  (ρ : Renameᵗ) →
  GenSafeSource A →
  GenSafeSource (renameᵗ ρ A)
renameGenSafeSource ρ source-fun = source-fun
renameGenSafeSource ρ source-all = source-all

substGenSafeSource :
  ∀ {A} →
  (cons : Substᵗ) →
  GenSafeSource A →
  GenSafeSource (substᵗ cons A)
substGenSafeSource cons source-fun = source-fun
substGenSafeSource cons source-all = source-all

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
    → {{GenSafeSource A}}
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
