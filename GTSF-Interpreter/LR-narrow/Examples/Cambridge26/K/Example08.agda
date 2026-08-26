module LR-narrow.Examples.Cambridge26.K.Example08 where

-- File Charter:
--   * Checks generalization followed by re-instantiation of the X binder.

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
  (generalize-X K-X-dynamic)
  (instantiate-X (generalize-X K-X-dynamic))
  is-just is-just
