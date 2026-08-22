module LR-narrow.Examples.Cambridge26.Example15 where

-- File Charter:
--   * Checks Cambridge26 Example 15: generalized dynamic identity is
--     instantiated at `Nat` on the imprecise side.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import NuTerms using (_·_)
open import TypeCheck using (is-just)

example : ClosedExample
example =
  checked-example Nat Nat
    nat-reflexive
    nat-reflexive-c
    nat-reflexive-narrowing
  (id-at Nat · nat 0)
  (instantiate-at IdBody Nat (generalize-id id★) · nat 0)
  is-just is-just
