module LR-narrow.Examples.Cambridge26.K.Example06 where

-- File Charter:
--   * Checks a cast that independently instantiates K's X binder.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.K.Common
open import LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)

example : ClosedExample
example =
  checked-example PolyK X-dynamic-K
    poly-k-to-dynamic-first
    poly-k-to-dynamic-first-c
    poly-k-to-dynamic-first-narrowing
  k (instantiate-X k) is-just is-just
