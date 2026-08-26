module LR-narrow.Examples.Cambridge26.K.Example05 where

-- File Charter:
--   * Checks the diagonal from fully polymorphic K to fully dynamic K.

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
  k k★ is-just is-just
