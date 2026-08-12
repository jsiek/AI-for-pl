module LR-narrow.Examples.Cambridge26.K.Example16 where

-- File Charter:
--   * Applies fully dynamic K obtained in X-then-Y order.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.K.Common
open import LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings
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
  (instantiate-Y-after-X (instantiate-X k) · nat★ 42 · nat★ 69)
  is-just is-just
