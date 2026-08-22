module LR-narrow.Examples.Cambridge26.K.Example15 where

-- File Charter:
--   * Applies K with precise X and dynamic Y; its result remains precise.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.K.Common
open import LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import NuTerms using (_·_)
open import TypeCheck using (is-just)
open import Types using (★; X₀; _⇒_)

example : ClosedExample
example =
  checked-example Nat Nat
    nat-reflexive
    nat-reflexive-c
    nat-reflexive-narrowing
  (k-at Nat Nat · nat 42 · nat 69)
  (instantiate-at (X₀ ⇒ ★ ⇒ X₀) Nat (instantiate-Y k)
    · nat 42 · nat★ 69)
  is-just is-just
