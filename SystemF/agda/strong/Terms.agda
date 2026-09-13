module strong.Terms where

-- Strong System F v7 — terms, typing, and values.
-- Boundary bodies are term-closed; source nodes carry no explicit colours.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ; _[_]ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph

data Prim : Set where
  p+ : Prim
  p× : Prim

infix  9 `_
infix  9 $_
infix  9 #_
infixl 8 _•_[_]
infixl 7 _·_
infixl 6 _⊕[_]_
infix  6 ƛ_∙_
infix  6 Λ_
infix  5 ν_,_[_∣_]

data Term : Set where
  `_       : ℕ → Term
  $_       : ℕ → Term
  #_       : Bool → Term
  _⊕[_]_   : Term → Prim → Term → Term
  ƛ_∙_     : Ty → Term → Term
  _·_      : Term → Term → Term
  Λ_       : Term → Term
  _•_[_]   : Term → Ty → Ty → Term
  ν_,_[_∣_] : Store → Scope → Term → Conv → Term

Ctx : Set
Ctx = List Ty

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → ℕ → Ty → Set where
  here  : ∀ {Γ A} → (A ∷ Γ) ∋ zero ⦂ A
  there : ∀ {Γ x A B} → Γ ∋ x ⦂ A → (B ∷ Γ) ∋ suc x ⦂ A

⤊ : Ctx → Ctx
⤊ Γ = map ⇑ᵗ Γ

infix 3 _∣_⊢_⦂_
data _∣_⊢_⦂_ : Ctxᵗ → Ctx → Term → Ty → Set where
  ⊢` : ∀ {Δ Γ x A} → Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ ` x ⦂ A
  ⊢$ : ∀ {Δ Γ n} → Δ ∣ Γ ⊢ $ n ⦂ `ℕ
  ⊢# : ∀ {Δ Γ b} → Δ ∣ Γ ⊢ # b ⦂ `𝔹
  ⊢⊕ : ∀ {Δ Γ M N p}
    → Δ ∣ Γ ⊢ M ⦂ `ℕ → Δ ∣ Γ ⊢ N ⦂ `ℕ
    → Δ ∣ Γ ⊢ M ⊕[ p ] N ⦂ `ℕ
  ⊢ƛ : ∀ {Δ Γ A B N}
    → Δ ⊢ᵗ A → Δ ∣ A ∷ Γ ⊢ N ⦂ B
    → Δ ∣ Γ ⊢ ƛ A ∙ N ⦂ A ⇒ B
  ⊢· : ∀ {Δ Γ A B L M}
    → Δ ∣ Γ ⊢ L ⦂ A ⇒ B → Δ ∣ Γ ⊢ M ⦂ A
    → Δ ∣ Γ ⊢ L · M ⦂ B
  ⊢Λ : ∀ {Δ Γ A N}
    → (name zero ∷ abst ∷ Δ) ∣ ⤊ Γ ⊢ N ⦂ A
    → Δ ∣ Γ ⊢ Λ N ⦂ `∀ A
  ⊢•[] : ∀ {Δ Γ A B L}
    → Δ ∣ Γ ⊢ L ⦂ `∀ B → Δ ⊢ᵗ A
    → Δ ∣ Γ ⊢ L • B [ A ] ⦂ B [ A ]ᵗ
  ⊢ν : ∀ {Δ ΔΘ Δᵢ Γ Θ χ M c A B}
    → Δ ⊢ˢ Θ ⇒ ΔΘ → ΔΘ ⊢χ χ ⇒ Δᵢ → NF c
    → Δᵢ ∣ [] ⊢ M ⦂ A → Δᵢ ⊢ c ∶ A ⇝ B ⊣ ΔΘ
    → Δ ∣ Γ ⊢ ν Θ , χ [ M ∣ c ] ⦂ B

data Literal : Term → Set where
  literal-$ : ∀ {n} → Literal ($ n)
  literal-# : ∀ {b} → Literal (# b)

data Applicable : Conv → Set where
  applies-arr : ∀ {c c₁ c₂}
    → arr c ≡ just (c₁ , c₂) → Applicable c
  applies-all : ∀ {c d}
    → allView c ≡ just d → Applicable c
  applies-var : ∀ {c X}
    → target c ≡ ` X → Applicable c

mutual
  data Simple : Term → Set where
    S$ : ∀ {n} → Simple ($ n)
    S# : ∀ {b} → Simple (# b)
    Sƛ : ∀ {A N} → Simple (ƛ A ∙ N)
    SΛ : ∀ {N} → Value N → Simple (Λ N)

  data Value : Term → Set where
    Vs : ∀ {V} → Simple V → Value V
    Vν : ∀ {Θ χ V c}
      → Simple V → NF c → Applicable c
      → Value (ν Θ , χ [ V ∣ c ])
