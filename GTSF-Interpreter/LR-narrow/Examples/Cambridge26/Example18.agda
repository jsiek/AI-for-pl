module LR-narrow.Examples.Cambridge26.Example18 where

-- File Charter:
--   * Checks Cambridge26 Example 18: polymorphic `K` is dynamically
--     instantiated twice on the imprecise side.

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
  (k-at Nat Nat · nat 42 · nat 69)
  (instantiate-k-dynamically k · nat★ 42 · nat★ 69)
  is-just is-just
