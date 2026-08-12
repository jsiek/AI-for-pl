module LR-narrow.Examples.Cambridge26.K.Example04 where

-- File Charter:
--   * Checks the K-lattice edge that makes X dynamic after Y is dynamic.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.K.Common
open import LR-narrow.Examples.Cambridge26.K.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)

example : ClosedExample
example =
  checked-example Y-dynamic-K DynK
    Y-dynamic-to-dynamic
    Y-dynamic-to-dynamic-c
    Y-dynamic-to-dynamic-narrowing
  K-Y-dynamic k★ is-just is-just
