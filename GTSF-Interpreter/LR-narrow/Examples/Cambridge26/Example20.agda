module LR-narrow.Examples.Cambridge26.Example20 where

-- File Charter:
--   * Checks the initial endpoint of Cambridge26 Example 20, isolated in the
--     note for the final branch of its one-sided universal-upcast argument.

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
  id (instantiate-id-dynamically (generalize-id id★))
  is-just is-just
