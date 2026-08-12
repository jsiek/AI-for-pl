module LR-narrow.Examples.Cambridge26.Example10 where

-- File Charter:
--   * Checks Cambridge26 Example 10: an instantiation cast is added on the
--     precise side of an otherwise dynamic application.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import NuTerms using (_·_)
open import TypeCheck using (is-just)
open import Types using (★)

example : ClosedExample
example =
  checked-example ★ ★
    dynamic-result
    dynamic-result-c
    dynamic-result-narrowing
  (instantiate-id-dynamically id · nat★ 0)
  (id★ · nat★ 0)
  is-just is-just
