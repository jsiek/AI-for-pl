module LR-narrow.Examples.Cambridge26.Example17 where

-- File Charter:
--   * Checks Cambridge26 Example 17 for the polymorphic and dynamic constant
--     functions, including both arguments omitted in the note's first line.

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
  (k★ · nat★ 42 · nat★ 69)
  is-just is-just
