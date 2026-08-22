module LR-narrow.Examples.Cambridge26.Example08 where

-- File Charter:
--   * Checks Cambridge26 Example 8: identity is instantiated at `Nat` on the
--     precise side and at `★` on the imprecise side.

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
  (id-at ★ · nat★ 0)
  is-just is-just
