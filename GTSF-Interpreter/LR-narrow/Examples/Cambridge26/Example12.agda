module LR-narrow.Examples.Cambridge26.Example12 where

-- File Charter:
--   * Checks Cambridge26 Example 12: one dynamic instantiation/generalization
--     round trip before precise `Nat` instantiation.
--   * No `split` or `extend` judgment is required at the closed endpoints.

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
  (instantiate-at IdBody Nat (round-trip-id id) · nat 0)
  is-just is-just
