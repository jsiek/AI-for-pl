module DerivationIso where

-- File Charter:
--   * Defines the reusable notion of an isomorphism between derivation sets.
--   * Requires both translations and propositional round trips.

open import Relation.Binary.PropositionalEquality using (_≡_)

record DerivationIso (P Q : Set) : Set where
  constructor derivation-iso
  field
    to : P → Q
    from : Q → P
    from-to : ∀ p → from (to p) ≡ p
    to-from : ∀ q → to (from q) ≡ q

open DerivationIso public
