module nu-cancel-id.Terms where

-- File Charter:
--   * TERMS, CONVERSIONS AND TYPING of νF₁ᶜ (notes/CancelIdSketch.md in
--     strong-rep-nu, on top of notes/SingleEntrySketch.md §§2–3).
--   * A boundary `[ s , α ] M ⟨ c ⟩` has ONE scope entry: a sign `s`
--     (`⁺` reveals cell α, `⁻` hides it) and a cell.  Its body is
--     term-closed and typed at the INTERIOR, where α's flag is set.
--   * Conversions mention no variables at all: `idᶜ` is untyped, and
--     `seal`/`unseal` act on the boundary's own cell.  So conversions
--     are typed against the store only, and never shift.
--   * Terms are typed at RUNTIME types (representation variables);
--     named types appear only in the annotations of `ƛ` and `ν`, read
--     through the flags (`_⊢_⇝_`).
--   * `Λ N` is a value for every body (no reduction under `Λ`).

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat using (ℕ; zero; suc)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx

------------------------------------------------------------------------
-- 1. Signs, conversions, constants, terms
------------------------------------------------------------------------

data Sign : Set where
  ⁺ ⁻ : Sign

flip : Sign → Sign
flip ⁺ = ⁻
flip ⁻ = ⁺

-- the cell's flag inside and outside a boundary with this sign
inside : Sign → Bool
inside ⁺ = true
inside ⁻ = false

outside : Sign → Bool
outside ⁺ = false
outside ⁻ = true

interior : Sign → ℕ → Ctx → Ctx
interior s α Γ = store Γ ∣ setFlag α (inside s) (flags Γ)

infixr 7 _↦_
data Conv : Set where
  idᶜ    : Conv
  _↦_    : Conv → Conv → Conv
  ∀ᶜ     : Conv → Conv
  seal   : Conv
  unseal : Conv

data Const : Set where
  nat  : ℕ → Const
  bool : Bool → Const

infixl 7 _·_
infix  5 ƛ_∙_
infix  5 Λ_

data Term : Set where
  `_          : ℕ → Term
  $_          : Const → Term
  ƛ_∙_        : Ty → Term → Term
  _·_         : Term → Term → Term
  Λ_          : Term → Term
  ν_·_⟨_⟩     : Ty → Term → Conv → Term       -- ν X:=A. (L X)⟨c⟩
  [_,_]_⟨_⟩   : Sign → ℕ → Term → Conv → Term

private
  variable
    Γ : Ctx
    Σ : Store
    Γₜ : List Ty
    s : Sign
    α x : ℕ
    A P R R′ S S′ : Ty
    c d : Conv
    L M N : Term
    n : ℕ
    b : Bool

------------------------------------------------------------------------
-- 2. Conversion typing, against the store and the boundary's entry
------------------------------------------------------------------------

infix 4 _∣_,_⊢_⦂_⟹_
data _∣_,_⊢_⦂_⟹_ : Store → Sign → ℕ → Conv → Ty → Ty → Set where
  c-id     : length Σ ⊢ʳ R
    → Σ ∣ s , α ⊢ idᶜ ⦂ R ⟹ R
  c-fun    : Σ ∣ flip s , α ⊢ c ⦂ R′ ⟹ R
    → Σ ∣ s , α ⊢ d ⦂ S ⟹ S′
    → Σ ∣ s , α ⊢ c ↦ d ⦂ R ⇒ S ⟹ R′ ⇒ S′
  c-all    : (abs ∷ Σ) ∣ s , suc α ⊢ c ⦂ R ⟹ S
    → Σ ∣ s , α ⊢ ∀ᶜ c ⦂ `∀ R ⟹ `∀ S
  c-seal   : Σ ∋ α := P
    → Σ ∣ ⁻ , α ⊢ seal ⦂ P ⟹ ` α
  c-unseal : Σ ∋ α := P
    → Σ ∣ ⁺ , α ⊢ unseal ⦂ ` α ⟹ P

------------------------------------------------------------------------
-- 3. Term typing
------------------------------------------------------------------------

infix 4 _∋ˣ_⦂_
data _∋ˣ_⦂_ : List Ty → ℕ → Ty → Set where
  x-here  : ∀ {Γₜ} → (R ∷ Γₜ) ∋ˣ zero ⦂ R
  x-there : ∀ {Γₜ} → Γₜ ∋ˣ x ⦂ R → (S ∷ Γₜ) ∋ˣ suc x ⦂ R

infix 4 _∣_⊢_⦂_
data _∣_⊢_⦂_ : Ctx → List Ty → Term → Ty → Set where
  ⊢`    : Γₜ ∋ˣ x ⦂ R
    → Γ ∣ Γₜ ⊢ ` x ⦂ R
  ⊢nat  : Γ ∣ Γₜ ⊢ $ nat n ⦂ `ℕ
  ⊢bool : Γ ∣ Γₜ ⊢ $ bool b ⦂ `𝔹
  ⊢ƛ    : flags Γ ⊢ A ⇝ R
    → Γ ∣ R ∷ Γₜ ⊢ N ⦂ S
    → Γ ∣ Γₜ ⊢ ƛ A ∙ N ⦂ R ⇒ S
  ⊢·    : Γ ∣ Γₜ ⊢ L ⦂ R ⇒ S
    → Γ ∣ Γₜ ⊢ M ⦂ R
    → Γ ∣ Γₜ ⊢ L · M ⦂ S
  ⊢Λ    : underΛ Γ ∣ map ⇑ᵗ Γₜ ⊢ N ⦂ R
    → Γ ∣ Γₜ ⊢ Λ N ⦂ `∀ R
  -- the instantiating conversion is typed where the new cell, with
  -- payload P, is allocated and named
  ⊢ν    : flags Γ ⊢ A ⇝ P
    → Γ ∣ Γₜ ⊢ L ⦂ `∀ R
    → (pay P ∷ store Γ) ∣ ⁺ , zero ⊢ c ⦂ R ⟹ ⇑ᵗ S
    → length (store Γ) ⊢ʳ S
    → Γ ∣ Γₜ ⊢ ν A · L ⟨ c ⟩ ⦂ S
  -- coherence: `⁺` needs α unnamed outside, `⁻` needs it named
  ⊢[]   : flags Γ ∋ᶠ α ⦂ outside s
    → interior s α Γ ∣ [] ⊢ M ⦂ R
    → store Γ ∣ s , α ⊢ c ⦂ R ⟹ S
    → Γ ∣ Γₜ ⊢ [ s , α ] M ⟨ c ⟩ ⦂ S
