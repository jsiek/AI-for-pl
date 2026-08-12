module LR-narrow.Examples.Cambridge26.K.Example02 where

-- File Charter:
--   * Checks the K-lattice edge from fully polymorphic K to Y-dynamic K.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.K.Common
open import LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)

example : ClosedExample
example =
  checked-example PolyK Y-dynamic-K
    poly-k-to-dynamic-second
    poly-k-to-dynamic-second-c
    poly-k-to-dynamic-second-narrowing
  k K-Y-dynamic is-just is-just
