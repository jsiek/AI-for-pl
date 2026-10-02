module GroundInterface where

-- File Charter:
--   * Public definitions for the Milestone 1 observer interface.
--   * Restricts boundary results to nat, unit, and ref nat.
--   * Hides concrete locations from labels; reads and writes address the one
--     reference capability returned at the boundary.
--   * Defines finite source executions that expose a ground result.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat
  renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.List using ([])
open import Data.Empty using (⊥)
open import Data.Product using (∃; ∃-syntax; _,_)

open import STLCRef

------------------------------------------------------------------------
-- Numerals and ground boundary results
------------------------------------------------------------------------

numeral : ℕ -> Term
numeral zeroℕ = `zero
numeral (sucℕ n) = `suc numeral n

value-numeral : (n : ℕ) -> Value (numeral n)
value-numeral zeroℕ = `zero
value-numeral (sucℕ n) = `suc value-numeral n

data GroundResult : Set where
  nat-result : ℕ -> GroundResult
  unit-result : GroundResult
  ref-result : ℕ -> GroundResult

------------------------------------------------------------------------
-- Observer states and public labels
------------------------------------------------------------------------

data State : Set where
  exposed : GroundResult -> Store -> State
  public-ref : ℕ -> Store -> State
  stopped : State
  diverging : State

-- The labels contain no concrete location. In Milestone 1 the sole public
-- reference is handle zero, so the location stored by `public-ref` is an
-- implementation detail.
data Label : Set where
  return-nat : ℕ -> Label
  return-unit : Label
  return-ref : Label
  read : ℕ -> Label
  write : ℕ -> Label

infix 3 _—[_]→ᵒ_
data _—[_]→ᵒ_ : State -> Label -> State -> Set where
  expose-nat : ∀ {n μ}
    -> exposed (nat-result n) μ —[ return-nat n ]→ᵒ stopped

  expose-unit : ∀ {μ}
    -> exposed unit-result μ —[ return-unit ]→ᵒ stopped

  expose-ref : ∀ {l μ}
    -> exposed (ref-result l) μ —[ return-ref ]→ᵒ public-ref l μ

  read-ref : ∀ {l μ n}
    -> lookupStore μ l ≡ just (numeral n)
    -> public-ref l μ —[ read n ]→ᵒ public-ref l μ

  write-ref : ∀ {l μ μ′ n}
    -> updateStore μ l (numeral n) ≡ just μ′
    -> public-ref l μ —[ write n ]→ᵒ public-ref l μ′

------------------------------------------------------------------------
-- Finite execution from a closed source term to a ground result
------------------------------------------------------------------------

infix 3 _⇓[_]_
data _⇓[_]_ (M : Term) : GroundResult -> Store -> Set where
  returns-nat : ∀ {n μ}
    -> [] ∣ [] ⊢ M ⦂ nat
    -> (M , []) —↠ (numeral n , μ)
    -> M ⇓[ nat-result n ] μ

  returns-unit : ∀ {μ}
    -> [] ∣ [] ⊢ M ⦂ unit
    -> (M , []) —↠ (`unit , μ)
    -> M ⇓[ unit-result ] μ

  returns-ref : ∀ {l μ}
    -> [] ∣ [] ⊢ M ⦂ ref nat
    -> (M , []) —↠ (`loc l , μ)
    -> M ⇓[ ref-result l ] μ

initial-state : ∀ {M r μ} -> M ⇓[ r ] μ -> State
initial-state {r = r} {μ = μ} execution = exposed r μ

GroundConverges : Term -> Set
GroundConverges M = ∃[ r ] ∃[ μ ] M ⇓[ r ] μ

GroundDiverges : Term -> Set
GroundDiverges M = GroundConverges M -> ⊥

initial-diverging-state : ∀ {M} -> GroundDiverges M -> State
initial-diverging-state divergence = diverging
