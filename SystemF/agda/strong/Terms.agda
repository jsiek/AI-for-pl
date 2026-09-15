module strong.Terms where

-- Strong System F v8 — terms, values, and typing.
--
-- The boundary is conversion application `M ⟨ c ⟩`: no store, no scope.
-- `ν R ∙ M` binds a local address with its representation, awaiting
-- discharge into the global store.  `Λ V` binds an address and a name:
-- its typing pushes the address binder and a CROSSING assignment for
-- it, and restricts the body to a VALUE, so there is no reduction under
-- `Λ`.  Boundary bodies are term-closed; ν bodies are not.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ; _[_]ᵗ)
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion

data Prim : Set where
  p+ : Prim
  p× : Prim

infix  9 `_
infix  9 $_
infix  9 #_
infixl 8 _•_[_]
infixl 8 _⟨_⟩
infixl 7 _·_
infixl 6 _⊕[_]_
infix  6 ƛ_∙_
infix  6 Λ_
infix  5 ν_∙_

data Term : Set where
  `_     : ℕ → Term
  $_     : ℕ → Term
  #_     : Bool → Term
  _⊕[_]_ : Term → Prim → Term → Term
  ƛ_∙_   : Ty → Term → Term
  _·_    : Term → Term → Term
  Λ_     : Term → Term
  _•_[_] : Term → Ty → Ty → Term
  ν_∙_   : RepTy → Term → Term
  _⟨_⟩   : Term → Conv → Term

data Literal : Term → Set where
  literal-$ : ∀ {n} → Literal ($ n)
  literal-# : ∀ {b} → Literal (# b)

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------
-- Term variables are NOT values; a `Λ` body is a value with, possibly,
-- free term variables under an inner λ.  An allocation is never a
-- value: in evaluation position it discharges.  A literal boundary with
-- a `base`-defined conversion is not a value: it steps by `Const`.

-- INERT conversions, in the sense of Siek and Chen's parameterized
-- cast calculi (see the PDF in this directory): a conversion that is
-- PART OF A VALUE.  It is inert exactly when an elimination can still
-- consume it — `arr` splits it at an application, `allView` at a type
-- application — or when its target is a type variable, the SEALED case
-- where no elimination applies and the boundary is genuinely opaque
-- until a later composition cancels the seal.  The complementary
-- ACTIVE conversions are the ones a step consumes on the spot: `base`
-- sees through a ground one and `Const` discards it.
data Inert : Conv → Set where
  inert-arr : ∀ A₀ {c c₁ c₂}
    → arr A₀ c ≡ just (c₁ , c₂) → Inert c
  inert-all : ∀ {c d}
    → allView c ≡ just d → Inert c
  inert-var : ∀ {c X}
    → target c ≡ ` X → Inert c

mutual
  data Simple : Term → Set where
    S$ : ∀ {n} → Simple ($ n)
    S# : ∀ {b} → Simple (# b)
    Sƛ : ∀ {A N} → Simple (ƛ A ∙ N)
    SΛ : ∀ {V} → Value V → Simple (Λ V)

  data Value : Term → Set where
    Vs  : ∀ {V} → Simple V → Value V
    V⟨⟩ : ∀ {V c}
      → Simple V → NF c → Inert c
      → Value (V ⟨ c ⟩)

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

Ctx : Set
Ctx = List Ty

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → ℕ → Ty → Set where
  here  : ∀ {Γ A} → (A ∷ Γ) ∋ zero ⦂ A
  there : ∀ {Γ x A B} → Γ ∋ x ⦂ A → (B ∷ Γ) ∋ suc x ⦂ A

-- Crossing into a `Λ` adds one name entry (the crossing assignment), so
-- the term context's types shift by one name.
⤊ : Ctx → Ctx
⤊ Γ = map ⇑ᵗ Γ

infix 3 _∣_∣_⊢_⦂_
data _∣_∣_⊢_⦂_ (Σ : Store) : Ctxᵗ → Ctx → Term → Ty → Set where
  ⊢` : ∀ {Δ Γ x A} → Γ ∋ x ⦂ A → Σ ∣ Δ ∣ Γ ⊢ ` x ⦂ A
  ⊢$ : ∀ {Δ Γ n} → Σ ∣ Δ ∣ Γ ⊢ $ n ⦂ `ℕ
  ⊢# : ∀ {Δ Γ b} → Σ ∣ Δ ∣ Γ ⊢ # b ⦂ `𝔹
  ⊢⊕ : ∀ {Δ Γ M N p}
    → Σ ∣ Δ ∣ Γ ⊢ M ⦂ `ℕ → Σ ∣ Δ ∣ Γ ⊢ N ⦂ `ℕ
    → Σ ∣ Δ ∣ Γ ⊢ M ⊕[ p ] N ⦂ `ℕ
  ⊢ƛ : ∀ {Δ Γ A B N}
    → Δ ⊢ᵗ A → Σ ∣ Δ ∣ (A ∷ Γ) ⊢ N ⦂ B
    → Σ ∣ Δ ∣ Γ ⊢ ƛ A ∙ N ⦂ A ⇒ B
  ⊢· : ∀ {Δ Γ A B L M}
    → Σ ∣ Δ ∣ Γ ⊢ L ⦂ A ⇒ B → Σ ∣ Δ ∣ Γ ⊢ M ⦂ A
    → Σ ∣ Δ ∣ Γ ⊢ L · M ⦂ B
  -- `Λ` binds an address (its binder) and pushes the crossing
  -- assignment naming it; the body is a VALUE.
  ⊢Λ : ∀ {Δ Γ A V}
    → Value V
    → Σ ∣ (asgn (bnd zero) ∷ addr ∷ Δ) ∣ ⤊ Γ ⊢ V ⦂ A
    → Σ ∣ Δ ∣ Γ ⊢ Λ V ⦂ `∀ A
  ⊢•[] : ∀ {Δ Γ A B L}
    → Σ ∣ Δ ∣ Γ ⊢ L ⦂ `∀ B → Δ ⊢ᵗ A
    → Σ ∣ Δ ∣ Γ ⊢ L • B [ A ] ⦂ B [ A ]ᵗ
  -- An allocation: the ν-bound entry adds no name, so neither the term
  -- context nor the result type shifts; addresses never appear in
  -- types, so A cannot leak the binder.
  ⊢ν : ∀ {Δ Γ R M A}
    → Σ ∣ Δ ⊢ᴿ R
    → Σ ∣ (nuBind R ∷ Δ) ∣ Γ ⊢ M ⦂ A
    → Σ ∣ Δ ∣ Γ ⊢ ν R ∙ M ⦂ A
  -- The boundary: the conversion's typing determines the interior
  -- context; the body is term-closed with respect to the exterior.
  ⊢⟨⟩ : ∀ {Δ Δᵢ Γ M c A B}
    → NF c
    → Σ ∣ Δᵢ ∣ [] ⊢ M ⦂ A
    → Σ ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ
    → Σ ∣ Δ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B
