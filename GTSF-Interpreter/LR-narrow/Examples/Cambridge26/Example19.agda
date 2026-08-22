module LR-narrow.Examples.Cambridge26.Example19 where

-- File Charter:
--   * Checks Cambridge26 Example 19, including the inner type application
--     whose allocated seal is rebound to the surrounding abstract type.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import NuTerms using (`_; ƛ_; _·_)
open import TypeCheck using (is-just)
open import Types using (★)

dynamic-rebinding-id : NuTerms.Term
dynamic-rebinding-id = ƛ ((ƛ (` 0)) · (` 0))

example : ClosedExample
example =
  checked-example Nat ★
    nat-to-dynamic
    nat-to-dynamic-c
    nat-to-dynamic-narrowing
  (instantiate-at IdBody Nat rebinding-id · nat 0)
  (dynamic-rebinding-id · nat★ 0)
  is-just is-just
