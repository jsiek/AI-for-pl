module LR-narrow.Examples.Cambridge26.Example06 where

-- File Charter:
--   * Checks the updated Cambridge26 Example 6 using an explicit `ν`
--     specialization and a mismatching ground argument.
--   * As in Example 5, a tagged function supplies the second ground tag that
--     the repository's natural-number-only primitive language lacks.

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
  (as-dynamic-nat-function (id-at Nat) · wrong-ground-argument)
  (id★ · wrong-ground-argument)
  is-just is-just
