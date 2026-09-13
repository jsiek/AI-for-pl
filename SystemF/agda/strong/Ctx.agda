module strong.Ctx where

-- Strong System F v7 — type/anchor contexts.
--
-- A context is ordered lexically, but its two variable classes use separate
-- de Bruijn coordinates: `name α` binds one source type variable and points
-- into the anchor universe; `abst` and `bind R` bind one anchor and no source
-- type variable.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.RepresentationTypes

data Ent : Set where
  abst : Ent
  bind : RepTy → Ent
  name : Anchor → Ent

data AnchorBinding : Set where
  abstA : AnchorBinding
  bindA : RepTy → AnchorBinding

Ctxᵗ : Set
Ctxᵗ = List Ent

private
  variable
    Δ : Ctxᵗ
    X Y : ℕ
    α β : Anchor
    A B : Ty
    R S : RepTy

infix 4 _∋a_
data _∋a_ : Ctxᵗ → Anchor → Set where
  a-here-abst : (abst ∷ Δ) ∋a zero
  a-here-bind : (bind R ∷ Δ) ∋a zero
  a-over-abst : Δ ∋a α → (abst ∷ Δ) ∋a suc α
  a-over-bind : Δ ∋a α → (bind R ∷ Δ) ∋a suc α
  a-over-name : Δ ∋a α → (name β ∷ Δ) ∋a α

infix 4 _∋ab_:=_
data _∋ab_:=_ : Ctxᵗ → Anchor → AnchorBinding → Set where
  ab-here-abst : (abst ∷ Δ) ∋ab zero := abstA
  ab-here-bind : (bind R ∷ Δ) ∋ab zero := bindA R
  ab-over-abst : ∀ {b} → Δ ∋ab α := b → (abst ∷ Δ) ∋ab suc α := b
  ab-over-bind : ∀ {b} → Δ ∋ab α := b → (bind R ∷ Δ) ∋ab suc α := b
  ab-over-name : ∀ {b} → Δ ∋ab α := b → (name X ∷ Δ) ∋ab α := b

infix 4 _∋tv_
data _∋tv_ : Ctxᵗ → ℕ → Set where
  tv-here       : (name α ∷ Δ) ∋tv zero
  tv-over-name  : Δ ∋tv X → (name α ∷ Δ) ∋tv suc X
  tv-over-abst  : Δ ∋tv X → (abst ∷ Δ) ∋tv X
  tv-over-bind  : Δ ∋tv X → (bind R ∷ Δ) ∋tv X

-- The anchor named by a source type variable.
infix 4 _∋n_:=_
data _∋n_:=_ : Ctxᵗ → ℕ → Anchor → Set where
  n-here       : (name α ∷ Δ) ∋n zero := α
  n-over-name  : Δ ∋n X := α → (name β ∷ Δ) ∋n suc X := α
  n-over-abst  : Δ ∋n X := α → (abst ∷ Δ) ∋n X := suc α
  n-over-bind  : Δ ∋n X := α → (bind R ∷ Δ) ∋n X := suc α

-- A represented anchor.  The result is shifted into the whole context.
infix 4 _∋r_:=_
data _∋r_:=_ : Ctxᵗ → Anchor → RepTy → Set where
  r-here       : (bind R ∷ Δ) ∋r zero := ⇑ᴿ R
  r-over-abst  : Δ ∋r α := R → (abst ∷ Δ) ∋r suc α := ⇑ᴿ R
  r-over-bind  : Δ ∋r α := R → (bind S ∷ Δ) ∋r suc α := ⇑ᴿ R
  r-over-name  : Δ ∋r α := R → (name β ∷ Δ) ∋r α := R

Unoccupied : Ctxᵗ → Anchor → Set
Unoccupied Δ α = ∀ X → ¬ (Σ[ β ∈ Anchor ] ((Δ ∋n X := β) × (β ≡ α)))

infix 4 _⊢ᵗ_
data _⊢ᵗ_ : Ctxᵗ → Ty → Set where
  wf-var : Δ ∋tv X → Δ ⊢ᵗ ` X
  wf-ℕ   : Δ ⊢ᵗ `ℕ
  wf-𝔹   : Δ ⊢ᵗ `𝔹
  wf-⇒   : Δ ⊢ᵗ A → Δ ⊢ᵗ B → Δ ⊢ᵗ (A ⇒ B)
  wf-∀   : (name zero ∷ abst ∷ Δ) ⊢ᵗ A → Δ ⊢ᵗ (`∀ A)

infix 4 _⊢ᴿ_
data _⊢ᴿ_ : Ctxᵗ → RepTy → Set where
  wfᴿ-var : Δ ∋a α → Δ ⊢ᴿ `α α
  wfᴿ-ℕ   : Δ ⊢ᴿ `ℕᴿ
  wfᴿ-𝔹   : Δ ⊢ᴿ `𝔹ᴿ
  wfᴿ-⇒   : Δ ⊢ᴿ R → Δ ⊢ᴿ S → Δ ⊢ᴿ (R ⇒ᴿ S)
  wfᴿ-∀   : (abst ∷ Δ) ⊢ᴿ R → Δ ⊢ᴿ (`∀ᴿ R)

data Base : Ty → Set where
  base-ℕ : Base `ℕ
  base-𝔹 : Base `𝔹

base-wf : Base A → Δ ⊢ᵗ A
base-wf base-ℕ = wf-ℕ
base-wf base-𝔹 = wf-𝔹

-- Quoting a source type into the anchor universe.
infix 4 _⊢⌊_⌋_
data _⊢⌊_⌋_ : Ctxᵗ → Ty → RepTy → Set where
  quote-var : Δ ∋n X := α → Δ ⊢⌊ ` X ⌋ `α α
  quote-ℕ   : Δ ⊢⌊ `ℕ ⌋ `ℕᴿ
  quote-𝔹   : Δ ⊢⌊ `𝔹 ⌋ `𝔹ᴿ
  quote-⇒   : Δ ⊢⌊ A ⌋ R → Δ ⊢⌊ B ⌋ S → Δ ⊢⌊ A ⇒ B ⌋ R ⇒ᴿ S
  quote-∀   : (name zero ∷ abst ∷ Δ) ⊢⌊ A ⌋ R
            → Δ ⊢⌊ `∀ A ⌋ `∀ᴿ R

-- Reading anchors through the source names visible at an endpoint.
infix 4 _⊢_⇓_
data _⊢_⇓_ : Ctxᵗ → RepTy → Ty → Set where
  read-var : Δ ∋n X := α → Δ ⊢ `α α ⇓ ` X
  read-ℕ   : Δ ⊢ `ℕᴿ ⇓ `ℕ
  read-𝔹   : Δ ⊢ `𝔹ᴿ ⇓ `𝔹
  read-⇒   : Δ ⊢ R ⇓ A → Δ ⊢ S ⇓ B → Δ ⊢ R ⇒ᴿ S ⇓ A ⇒ B
  read-∀   : (name zero ∷ abst ∷ Δ) ⊢ R ⇓ A
           → Δ ⊢ `∀ᴿ R ⇓ `∀ A

infix 4 _ok
data _ok : Ctxᵗ → Set where
  ok[]    : [] ok
  ok-abst : Δ ok → (abst ∷ Δ) ok
  ok-bind : Δ ok → Δ ⊢ᴿ R → (bind R ∷ Δ) ok
  ok-name : Δ ok → Δ ∋a α → Unoccupied Δ α → (name α ∷ Δ) ok

VarSet : Set
VarSet = List ℕ

scopeᵗ : Ctxᵗ → VarSet
scopeᵗ []           = []
scopeᵗ (abst ∷ Δ)   = scopeᵗ Δ
scopeᵗ (bind R ∷ Δ) = scopeᵗ Δ
scopeᵗ (name α ∷ Δ) = zero ∷ map suc (scopeᵗ Δ)

anchorCount : Ctxᵗ → ℕ
anchorCount []           = zero
anchorCount (abst ∷ Δ)   = suc (anchorCount Δ)
anchorCount (bind R ∷ Δ) = suc (anchorCount Δ)
anchorCount (name α ∷ Δ) = anchorCount Δ

anchorLevel : Ctxᵗ → Anchor → ℕ
anchorLevel Δ α = anchorCount Δ ∸ suc α

data SameAnchor (Δ₁ : Ctxᵗ) (α : Anchor)
                (Δ₂ : Ctxᵗ) (β : Anchor) : Set where
  same-anchor : ∀ {b} → Δ₁ ∋ab α := b → Δ₂ ∋ab β := b
              → anchorLevel Δ₁ α ≡ anchorLevel Δ₂ β
              → SameAnchor Δ₁ α Δ₂ β

-- The first k source variables are binders introduced in parallel while
-- descending through structural `∀` conversions.
data Paired : ℕ → ℕ → Set where
  paired-zero : ∀ {k} → Paired (suc k) zero
  paired-suc  : ∀ {k X} → Paired k X → Paired (suc k) (suc X)

data SameTy (k : ℕ) (Δ₁ : Ctxᵗ) : Ty → Ctxᵗ → Ty → Set where
  same-bound : ∀ {X Δ₂} → Paired k X
             → SameTy k Δ₁ (` X) Δ₂ (` X)
  same-free  : ∀ {X Y α β Δ₂}
             → Δ₁ ∋n X := α → Δ₂ ∋n Y := β
             → SameAnchor Δ₁ α Δ₂ β
             → SameTy k Δ₁ (` X) Δ₂ (` Y)
  same-ℕ     : ∀ {Δ₂} → SameTy k Δ₁ `ℕ Δ₂ `ℕ
  same-𝔹     : ∀ {Δ₂} → SameTy k Δ₁ `𝔹 Δ₂ `𝔹
  same-⇒     : ∀ {A B C D Δ₂}
             → SameTy k Δ₁ A Δ₂ C → SameTy k Δ₁ B Δ₂ D
             → SameTy k Δ₁ (A ⇒ B) Δ₂ (C ⇒ D)
  same-∀     : ∀ {A B Δ₂}
             → SameTy (suc k) (name zero ∷ abst ∷ Δ₁) A
                                (name zero ∷ abst ∷ Δ₂) B
             → SameTy k Δ₁ (`∀ A) Δ₂ (`∀ B)
