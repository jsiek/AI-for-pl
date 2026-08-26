module LR-narrow.Examples.Cambridge26.K.Example11 where

-- File Charter:
--   * Checks a Y-only instantiation/generalization round trip.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.K.Common
open import LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)

example : ClosedExample
example =
  checked-example PolyK PolyK
    poly-k-reflexive
    poly-k-reflexive-c
    poly-k-reflexive-narrowing
  k (generalize-Y (instantiate-Y k)) is-just is-just
