module LR-narrow.Examples.Cambridge26.K.Example14 where

-- File Charter:
--   * Applies K with dynamic X and precise Y; its result becomes dynamic.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.K.Common
open import LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import NuTerms using (_·_)
open import TypeCheck using (is-just)
open import Types using (★; X₀; _⇒_)

example : ClosedExample
example =
  checked-example Nat ★
    nat-to-dynamic
    nat-to-dynamic-c
    nat-to-dynamic-narrowing
  (k-at Nat Nat · nat 42 · nat 69)
  (instantiate-at (★ ⇒ X₀ ⇒ ★) Nat (instantiate-X k)
    · nat★ 42 · nat 69)
  is-just is-just
