module LR-narrow.Examples.Cambridge26.K.Example03 where

-- File Charter:
--   * Checks the K-lattice edge that makes Y dynamic after X is dynamic.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.K.Common
open import LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)

example : ClosedExample
example =
  checked-example X-dynamic-K DynK
    X-dynamic-to-dynamic
    X-dynamic-to-dynamic-c
    X-dynamic-to-dynamic-narrowing
  K-X-dynamic k★ is-just is-just
