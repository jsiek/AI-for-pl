module LR-narrow.Examples.Cambridge26.K.Example13 where

-- File Charter:
--   * Checks complete dynamic instantiation in Y-then-X order.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.K.Common
open import LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)

example : ClosedExample
example =
  checked-example PolyK DynK
    poly-k-to-dynamic
    poly-k-to-dynamic-c
    poly-k-to-dynamic-narrowing
  k (instantiate-X-after-Y (instantiate-Y k)) is-just is-just
