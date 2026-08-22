module LR-narrow.Examples.Cambridge26.Example16 where

-- File Charter:
--   * Checks Cambridge26 Example 16: generalized dynamic identity at `Nat`
--     remains more precise than direct dynamic identity.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import NuTerms using (_·_)
open import TypeCheck using (is-just)
open import Types using (★)

example : ClosedExample
example =
  checked-example Nat ★
    nat-to-dynamic
    nat-to-dynamic-c
    nat-to-dynamic-narrowing
  (instantiate-at IdBody Nat (generalize-id id★) · nat 0)
  (id★ · nat★ 0)
  is-just is-just
