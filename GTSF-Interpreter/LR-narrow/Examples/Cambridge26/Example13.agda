module LR-narrow.Examples.Cambridge26.Example13 where

-- File Charter:
--   * Checks Cambridge26 Example 13: one round trip followed by dynamic
--     instantiation.

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
  (id-at Nat · nat 0)
  (instantiate-id-dynamically (round-trip-id id) · nat★ 0)
  is-just is-just
