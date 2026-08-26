module LR-narrow.Examples.Cambridge26.K.Example07 where

-- File Charter:
--   * Checks a cast that independently instantiates K's Y binder.

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
  k (instantiate-Y k) is-just is-just
