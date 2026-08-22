module LR-narrow.Examples.Cambridge26.Example02 where

-- File Charter:
--   * Checks Cambridge26 Example 2 at its initial closed endpoints.

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
