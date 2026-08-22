module LR-narrow.Examples.Cambridge26.Example01 where

-- File Charter:
--   * Checks Cambridge26 Example 1 at its initial closed endpoints.
--   * The LR orientation puts dynamic `id` on the imprecise left.

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
  id (instantiate-id-dynamically (generalize-id id★)) is-just is-just
