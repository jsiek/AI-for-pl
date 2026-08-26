module LR-narrow.Examples.Cambridge26.Example04 where

-- File Charter:
--   * Checks Cambridge26 Example 4 without the obsolete `split` rule.
--   * The interpreter allocates the two physical seals; their pairing belongs
--     to the Kripke world rather than to type imprecision.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)

example : ClosedExample
example =
  checked-example PolyId DynId
    poly-id-to-dynamic
    poly-id-to-dynamic-c
    poly-id-to-dynamic-narrowing
  id (instantiate-id-dynamically id) is-just is-just
