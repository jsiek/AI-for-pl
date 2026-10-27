module GradualityDefinitions where

-- File Charter:
--   * The vocabulary of the graduality theorem for PolyCν: observations
--     of values, convergence, failure, and divergence (also divergence
--     or failure) of a closed term run from the empty store.

open import Data.Bool using (Bool; true; false)
open import Data.List using ([])
open import Data.Product using (∃-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Terms
open import Reduction

------------------------------------------------------------------------
-- Observations: a boolean, or something else; seals and injections
-- are looked through
------------------------------------------------------------------------

data Observation : Set where
  bool-obs  : Bool → Observation
  other-obs : Observation

observe : ∀ {V} → Value V → Observation
observe V-true = bool-obs true
observe V-false = bool-obs false
observe V-ƛ = other-obs
observe V-Λν = other-obs
observe (V-seal v) = observe v
observe (V-inj v) = observe v
observe (V-cast⇒ v) = other-obs

------------------------------------------------------------------------
-- Runs from the empty store
------------------------------------------------------------------------

-- M reaches the value V
_⇓_ : Term → Term → Set
M ⇓ V = ∃[ Σ ] (([] ▷ M —↠ Σ ▷ V) × Value V)

-- M fails with a dynamic type error
Fails : Term → Set
Fails M = ∃[ Σ ] ([] ▷ M —↠ Σ ▷ ℧)

-- every term M reaches can take a step
Diverges : Term → Set
Diverges M =
  ∀ {Σ N} → [] ▷ M —↠ Σ ▷ N → ∃[ Σ′ ] ∃[ N′ ] (Σ ▷ N —→ Σ′ ▷ N′)

-- every term M reaches can take a step or is ℧
DivergesOrFails : Term → Set
DivergesOrFails M =
  ∀ {Σ N} → [] ▷ M —↠ Σ ▷ N
  → ∃[ Σ′ ] ∃[ N′ ] (Σ ▷ N —→ Σ′ ▷ N′) ⊎ N ≡ ℧
