module LR-narrow.Examples.Cambridge26.Example21 where

-- File Charter:
--   * Checks Cambridge26 Example 21 (the double-`ν` downcast example).
--   * The note's `split` step is represented semantically by separate fresh
--     bindings in the LR world, not by extending type imprecision.

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
  (generalize-id id★)
  (instantiate-id-dynamically (generalize-id id★))
  is-just is-just
