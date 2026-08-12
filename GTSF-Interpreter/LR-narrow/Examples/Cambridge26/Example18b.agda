module LR-narrow.Examples.Cambridge26.Example18b where

-- File Charter:
--   * Checks Cambridge26 Example 18b: dynamic `K` is generalized twice and
--     then instantiated precisely twice.

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
  (k-at Nat Nat · nat 42 · nat 69)
  (k-at-from Nat Nat (generalize-k k★) · nat 42 · nat 69)
  is-just is-just
