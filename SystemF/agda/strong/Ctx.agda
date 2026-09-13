module strong.Ctx where

-- Strong System F v7 — type/anchor contexts, merged entries.
--
-- A context entry is an ANCHOR, carrying its binding and whether a source
-- name currently stands for it.  The two variable classes keep their
-- separate roles and get separate, clean coordinates:
--
--   an ANCHOR's index is its POSITION.  Anchors are introduced by a store
--   or a `∀` and are never removed, so they have the big, stable scope.
--
--   a TYPE VARIABLE's index counts the REVEALED entries.  It enters scope
--   at a reveal and leaves at a conceal, which is what colour preservation
--   is about.
--
-- The `_∋n_:=_` rules below are where the difference lives: every step
-- raises the anchor, and only a revealed step raises the type variable.
--
-- Because a reveal and a conceal FLIP A BIT rather than add or remove an
-- entry, they are LENGTH-PRESERVING: anchor indices are stable across a
-- boundary, so `SameAnchor` is plain index equality and no de Bruijn LEVEL
-- is needed.  See notes/probes/V7MergedEntryProbe.agda.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.RepresentationTypes

data AnchorBinding : Set where
  abstA : AnchorBinding
  bindA : RepTy → AnchorBinding

data Vis : Set where
  concealed : Vis
  revealed  : Vis

data Ent : Set where
  anch : Vis → AnchorBinding → Ent

Ctxᵗ : Set
Ctxᵗ = List Ent

private
  variable
    Δ : Ctxᵗ
    X Y : ℕ
    α β : Anchor
    A B : Ty
    R S : RepTy
    v w : Vis
    b : AnchorBinding
    e : Ent

-- Anchors index the context directly.
anchorCount : Ctxᵗ → ℕ
anchorCount = length

infix 4 _∋a_
data _∋a_ : Ctxᵗ → Anchor → Set where
  a-here  : (e ∷ Δ) ∋a zero
  a-there : Δ ∋a α → (e ∷ Δ) ∋a suc α

infix 4 _∋ab_:=_
data _∋ab_:=_ : Ctxᵗ → Anchor → AnchorBinding → Set where
  ab-here  : (anch v b ∷ Δ) ∋ab zero := b
  ab-there : Δ ∋ab α := b → (e ∷ Δ) ∋ab suc α := b

-- Type variables index the REVEALED entries.
infix 4 _∋tv_
data _∋tv_ : Ctxᵗ → ℕ → Set where
  tv-here      : (anch revealed b ∷ Δ) ∋tv zero
  tv-revealed  : Δ ∋tv X → (anch revealed b ∷ Δ) ∋tv suc X
  tv-concealed : Δ ∋tv X → (anch concealed b ∷ Δ) ∋tv X

-- The anchor a source type variable names.  EVERY step raises the anchor;
-- only a REVEALED step raises the type variable.
infix 4 _∋n_:=_
data _∋n_:=_ : Ctxᵗ → ℕ → Anchor → Set where
  n-here       : (anch revealed b ∷ Δ) ∋n zero := zero
  n-revealed   : Δ ∋n X := α → (anch revealed b ∷ Δ) ∋n suc X := suc α
  n-concealed  : Δ ∋n X := α → (anch concealed b ∷ Δ) ∋n X := suc α

-- A represented anchor.  The result is shifted into the whole context.
infix 4 _∋r_:=_
data _∋r_:=_ : Ctxᵗ → Anchor → RepTy → Set where
  r-here  : (anch v (bindA R) ∷ Δ) ∋r zero := ⇑ᴿ R
  r-there : Δ ∋r α := R → (e ∷ Δ) ∋r suc α := ⇑ᴿ R

infix 4 _⊢ᵗ_
data _⊢ᵗ_ : Ctxᵗ → Ty → Set where
  wf-var : Δ ∋tv X → Δ ⊢ᵗ ` X
  wf-ℕ   : Δ ⊢ᵗ `ℕ
  wf-𝔹   : Δ ⊢ᵗ `𝔹
  wf-⇒   : Δ ⊢ᵗ A → Δ ⊢ᵗ B → Δ ⊢ᵗ (A ⇒ B)
  wf-∀   : (anch revealed abstA ∷ Δ) ⊢ᵗ A → Δ ⊢ᵗ (`∀ A)

-- Representation types mention anchors only, so visibility is irrelevant
-- to them; `∀ᴿ` binds an anchor with no source name.
infix 4 _⊢ᴿ_
data _⊢ᴿ_ : Ctxᵗ → RepTy → Set where
  wfᴿ-var : Δ ∋a α → Δ ⊢ᴿ `α α
  wfᴿ-ℕ   : Δ ⊢ᴿ `ℕᴿ
  wfᴿ-𝔹   : Δ ⊢ᴿ `𝔹ᴿ
  wfᴿ-⇒   : Δ ⊢ᴿ R → Δ ⊢ᴿ S → Δ ⊢ᴿ (R ⇒ᴿ S)
  wfᴿ-∀   : (anch concealed abstA ∷ Δ) ⊢ᴿ R → Δ ⊢ᴿ (`∀ᴿ R)

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
  quote-∀   : (anch revealed abstA ∷ Δ) ⊢⌊ A ⌋ R
            → Δ ⊢⌊ `∀ A ⌋ `∀ᴿ R

-- Reading anchors through the source names visible at an endpoint.
infix 4 _⊢_⇓_
data _⊢_⇓_ : Ctxᵗ → RepTy → Ty → Set where
  read-var : Δ ∋n X := α → Δ ⊢ `α α ⇓ ` X
  read-ℕ   : Δ ⊢ `ℕᴿ ⇓ `ℕ
  read-𝔹   : Δ ⊢ `𝔹ᴿ ⇓ `𝔹
  read-⇒   : Δ ⊢ R ⇓ A → Δ ⊢ S ⇓ B → Δ ⊢ R ⇒ᴿ S ⇓ A ⇒ B
  read-∀   : (anch revealed abstA ∷ Δ) ⊢ R ⇓ A
           → Δ ⊢ `∀ᴿ R ⇓ `∀ A

-- An anchor carries at most one name BY CONSTRUCTION, so there is nothing
-- left for a freshness side condition to check.
infix 4 _ok
data _ok : Ctxᵗ → Set where
  ok[]    : [] ok
  ok-abst : Δ ok → (anch v abstA ∷ Δ) ok
  ok-bind : Δ ok → Δ ⊢ᴿ R → (anch v (bindA R) ∷ Δ) ok

VarSet : Set
VarSet = List ℕ

-- The colour: exactly the revealed entries.
scopeᵗ : Ctxᵗ → VarSet
scopeᵗ []                       = []
scopeᵗ (anch revealed b ∷ Δ)    = zero ∷ map suc (scopeᵗ Δ)
scopeᵗ (anch concealed b ∷ Δ)   = scopeᵗ Δ

-- Two anchors are the same anchor when they have the same INDEX.  A reveal
-- or a conceal flips a bit and adds no entry, so an index means the same
-- anchor at a boundary's interior and its exterior alike.
data SameAnchor (Δ₁ : Ctxᵗ) (α : Anchor)
                (Δ₂ : Ctxᵗ) (β : Anchor) : Set where
  same-anchor : Δ₁ ∋a α → Δ₂ ∋a β → α ≡ β → SameAnchor Δ₁ α Δ₂ β

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
             → SameTy (suc k) (anch revealed abstA ∷ Δ₁) A
                              (anch revealed abstA ∷ Δ₂) B
             → SameTy k Δ₁ (`∀ A) Δ₂ (`∀ B)
