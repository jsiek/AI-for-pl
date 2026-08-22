module LR-narrow.Examples.Cambridge26.Example14 where

-- File Charter:
--   * Checks Cambridge26 Example 14: two dynamic round trips followed by
--     precise `Nat` instantiation.
--   * This is the reduction-free endpoint counterpart of the older
--     small-step experiment in `GTSF/proof/Quotient`.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import NuTerms using (_·_)
open import TypeCheck using (is-just)

example : ClosedExample
example =
  checked-example Nat Nat
    nat-reflexive
    nat-reflexive-c
    nat-reflexive-narrowing
  (id-at Nat · nat 0)
  (instantiate-at IdBody Nat (two-round-trips-id id) · nat 0)
  is-just is-just
