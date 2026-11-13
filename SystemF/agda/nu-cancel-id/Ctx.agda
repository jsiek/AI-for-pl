module nu-cancel-id.Ctx where

-- File Charter:
--   * THE RUNTIME CONTEXT: a STORE of representation cells and, beside
--     it, one NAMED flag per cell.  A cell is abstract (a `Λ`'s variable)
--     or holds a payload.  The flag says whether the cell has a name in
--     scope.
--   * WHY FLAGS.  Under the sketch's naming condition a representation
--     variable has one name for its whole life, so a name map is
--     determined by WHICH variables are named.  Names are then positions
--     among the named cells (`_∋ⁿ_↦_`), and a scope entry `±α` sets one
--     flag (`setFlag`).  Entries for different variables commute on the
--     nose, which is what Sink needs (notes/CancelIdSketch.md §4).
--   * §1 cells and contexts; §2 lookups (payload, flag, name); §3 flag
--     update; §4 spelling a named type as a runtime type.  Definitions
--     only.

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)

open import nu-cancel-id.Types

------------------------------------------------------------------------
-- 1. Cells and contexts
------------------------------------------------------------------------

-- A payload is stored outside its own cell: it may mention only older
-- cells, and a lookup shifts it into the reader's scope.
data Payload : Set where
  abs : Payload
  pay : Ty → Payload

Store : Set
Store = List Payload

Flags : Set
Flags = List Bool

infix 4 _∣_
record Ctx : Set where
  constructor _∣_
  field
    store : Store
    flags : Flags
open Ctx public

-- A `Λ` (and the premise of a `∀` conversion) binds a new abstract cell
-- with a name.
underΛ : Ctx → Ctx
underΛ Γ = (abs ∷ store Γ) ∣ (true ∷ flags Γ)

private
  variable
    Σ : Store
    Φ : Flags
    p : Payload
    b b′ : Bool
    P R S : Ty
    X α : ℕ
    n : ℕ

------------------------------------------------------------------------
-- 2. Lookups
------------------------------------------------------------------------

-- The payload of cell α, read in the store's scope.
infix 4 _∋_:=_
data _∋_:=_ : Store → ℕ → Ty → Set where
  p-here  : (pay P ∷ Σ) ∋ zero := ⇑ᵗ P
  p-there : Σ ∋ α := P → (p ∷ Σ) ∋ suc α := ⇑ᵗ P

-- The flag of cell α.
infix 4 _∋ᶠ_⦂_
data _∋ᶠ_⦂_ : Flags → ℕ → Bool → Set where
  f-here  : (b ∷ Φ) ∋ᶠ zero ⦂ b
  f-there : Φ ∋ᶠ α ⦂ b → (b′ ∷ Φ) ∋ᶠ suc α ⦂ b

-- Name X denotes cell α: α is the X-th named cell, newest first.
infix 4 _∋ⁿ_↦_
data _∋ⁿ_↦_ : Flags → ℕ → ℕ → Set where
  n-here   : (true ∷ Φ) ∋ⁿ zero ↦ zero
  n-named  : Φ ∋ⁿ X ↦ α → (true ∷ Φ) ∋ⁿ suc X ↦ suc α
  n-hidden : Φ ∋ⁿ X ↦ α → (false ∷ Φ) ∋ⁿ X ↦ suc α

------------------------------------------------------------------------
-- 3. Flag update: what a scope entry does to its interior
------------------------------------------------------------------------

setFlag : ℕ → Bool → Flags → Flags
setFlag α       b []       = []
setFlag zero    b (_ ∷ Φ)  = b ∷ Φ
setFlag (suc α) b (b′ ∷ Φ) = b′ ∷ setFlag α b Φ

------------------------------------------------------------------------
-- 4. Spelling: the runtime type a named type denotes
------------------------------------------------------------------------

infix 4 _⊢_⇝_
data _⊢_⇝_ : Flags → Ty → Ty → Set where
  s-var : Φ ∋ⁿ X ↦ α → Φ ⊢ ` X ⇝ ` α
  s-ℕ   : Φ ⊢ `ℕ ⇝ `ℕ
  s-𝔹   : Φ ⊢ `𝔹 ⇝ `𝔹
  s-⇒   : ∀ {A B} → Φ ⊢ A ⇝ R → Φ ⊢ B ⇝ S → Φ ⊢ A ⇒ B ⇝ R ⇒ S
  s-∀   : ∀ {A} → (true ∷ Φ) ⊢ A ⇝ R → Φ ⊢ `∀ A ⇝ `∀ R
