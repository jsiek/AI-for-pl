module Bisimulation where

-- File Charter:
--   * Core definitions for Milestone 1 observer bisimulation.
--   * Defines generic strong bisimulation and the canonical ground relation.
--   * Contains no theorem implementations.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Product using (∃; ∃-syntax; _×_)

open import STLCRef using (Store; lookupStore)
open import GroundInterface

record IsBisimulation (R : State -> State -> Set) : Set where
  field
    forth : ∀ {P Q a P′}
      -> R P Q
      -> P —[ a ]→ᵒ P′
      -> ∃[ Q′ ] (Q —[ a ]→ᵒ Q′) × R P′ Q′

    back : ∀ {P Q a Q′}
      -> R P Q
      -> Q —[ a ]→ᵒ Q′
      -> ∃[ P′ ] (P —[ a ]→ᵒ P′) × R P′ Q′

record _≈_ (P Q : State) : Set₁ where
  field
    Relation : State -> State -> Set
    is-bisimulation : IsBisimulation Relation
    related : Relation P Q

record KeyCorrespondence (μ : Store) (l : ℕ)
                         (ν : Store) (k : ℕ) : Set where
  constructor relate-key
  field
    contents-agree : lookupStore μ l ≡ lookupStore ν k
    left-natural : ∃[ n ] lookupStore μ l ≡ just (numeral n)

open KeyCorrespondence public

data GroundRelated : State -> State -> Set where
  stoppedᵣ : GroundRelated stopped stopped
  divergingᵣ : GroundRelated diverging diverging

  natᵣ : ∀ {n μ ν}
    -> GroundRelated (exposed (nat-result n) μ)
                     (exposed (nat-result n) ν)

  unitᵣ : ∀ {μ ν}
    -> GroundRelated (exposed unit-result μ) (exposed unit-result ν)

  exposed-refᵣ : ∀ {l k μ ν}
    -> KeyCorrespondence μ l ν k
    -> GroundRelated (exposed (ref-result l) μ)
                     (exposed (ref-result k) ν)

  public-refᵣ : ∀ {l k μ ν}
    -> KeyCorrespondence μ l ν k
    -> GroundRelated (public-ref l μ) (public-ref k ν)
