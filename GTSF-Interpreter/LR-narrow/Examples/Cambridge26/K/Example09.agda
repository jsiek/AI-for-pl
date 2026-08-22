module LR-narrow.Examples.Cambridge26.K.Example09 where

-- File Charter:
--   * Checks generalization followed by re-instantiation of the Y binder.

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
  (generalize-Y K-Y-dynamic)
  (instantiate-Y (generalize-Y K-Y-dynamic))
  is-just is-just
