module nu-cancel-id.Terms where

-- File Charter:
--   * TERMS, CONVERSIONS AND TYPING of νF₁ᶜ, second version
--     (notes/CancelIdSketch.md §8 in strong-rep-nu): terms are typed at
--     NAMED types.
--   * A boundary `[ s , α ] M ⟨ c ⟩` has ONE scope entry: a sign `s`
--     (`⁺` reveals cell α, `⁻` hides it) and a cell.  Its body is
--     term-closed and typed at the INTERIOR, where α's flag is set.  Its
--     interior and exterior types are named types, each read in its own
--     context (`_⊢_⇝_`), and the conversion relates the two readings.
--   * Conversions mention no variables at all: `idᶜ` is untyped, and
--     `seal`/`unseal` act on the boundary's own cell.  So conversions
--     are typed against the store only, at runtime types, and never
--     shift.
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
    A B C P R R′ S S′ : Ty
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
  x-here  : ∀ {Γₜ} → (A ∷ Γₜ) ∋ˣ zero ⦂ A
  x-there : ∀ {Γₜ} → Γₜ ∋ˣ x ⦂ A → (B ∷ Γₜ) ∋ˣ suc x ⦂ A

infix 4 _∣_⊢_⦂_
data _∣_⊢_⦂_ : Ctx → List Ty → Term → Ty → Set where
  ⊢`    : Γₜ ∋ˣ x ⦂ A
    → Γ ∣ Γₜ ⊢ ` x ⦂ A
  ⊢nat  : Γ ∣ Γₜ ⊢ $ nat n ⦂ `ℕ
  ⊢bool : Γ ∣ Γₜ ⊢ $ bool b ⦂ `𝔹
  ⊢ƛ    : flags Γ ⊢ A ⇝ R
    → Γ ∣ A ∷ Γₜ ⊢ N ⦂ B
    → Γ ∣ Γₜ ⊢ ƛ A ∙ N ⦂ A ⇒ B
  ⊢·    : Γ ∣ Γₜ ⊢ L ⦂ A ⇒ B
    → Γ ∣ Γₜ ⊢ M ⦂ A
    → Γ ∣ Γₜ ⊢ L · M ⦂ B
  ⊢Λ    : underΛ Γ ∣ map ⇑ᵗ Γₜ ⊢ N ⦂ C
    → Γ ∣ Γₜ ⊢ Λ N ⦂ `∀ C
  -- the instantiating conversion is typed where the new cell, with
  -- payload P, is allocated and named; the result type B is read
  -- beside the new cell, unnamed, which is TyBeta's exterior
  ⊢ν    : flags Γ ⊢ A ⇝ P
    → Γ ∣ Γₜ ⊢ L ⦂ `∀ C
    → (true ∷ flags Γ) ⊢ C ⇝ R
    → (false ∷ flags Γ) ⊢ B ⇝ S
    → (pay P ∷ store Γ) ∣ ⁺ , zero ⊢ c ⦂ R ⟹ S
    → Γ ∣ Γₜ ⊢ ν A · L ⟨ c ⟩ ⦂ B
  -- coherence: `⁺` needs α unnamed outside, `⁻` needs it named
  ⊢[]   : flags Γ ∋ᶠ α ⦂ outside s
    → interior s α Γ ∣ [] ⊢ M ⦂ A
    → flags (interior s α Γ) ⊢ A ⇝ R
    → flags Γ ⊢ B ⇝ S
    → store Γ ∣ s , α ⊢ c ⦂ R ⟹ S
    → Γ ∣ Γₜ ⊢ [ s , α ] M ⟨ c ⟩ ⦂ B
