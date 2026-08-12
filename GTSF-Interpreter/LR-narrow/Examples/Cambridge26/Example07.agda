module LR-narrow.Examples.Cambridge26.Example07 where

-- File Charter:
--   * Checks Cambridge26 Example 7: instantiation preserves the relation
--     between polymorphic identity and generalized dynamic identity.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)
open import Types using (_⇒_)

example : ClosedExample
example =
  checked-example (Nat ⇒ Nat) (Nat ⇒ Nat)
    nat-id
    nat-id-c
    nat-id-narrowing
  (id-at Nat)
  (instantiate-at IdBody Nat (generalize-id id★))
  is-just is-just
