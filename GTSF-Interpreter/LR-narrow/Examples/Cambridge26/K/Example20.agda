module LR-narrow.Examples.Cambridge26.K.Example20 where

-- File Charter:
--   * Checks raw dynamic K generalized directly to polymorphic K.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)

example : ClosedExample
example =
  checked-example PolyK PolyK
    poly-k-reflexive
    poly-k-reflexive-c
    poly-k-reflexive-narrowing
  k (generalize-k k★) is-just is-just
