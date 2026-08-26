module LR-narrow.Examples.Cambridge26.Example03 where

-- File Charter:
--   * Gives a closed, checked version of Cambridge26 Example 3.
--   * The note's open `extend` state is represented by compiling the precise
--     type application to `ν α := Nat`; no LR `extend` rule is assumed.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import TypeCheck using (is-just)
open import Types using (_⇒_)

example : ClosedExample
example =
  checked-example (Nat ⇒ Nat) DynId
    nat-function-to-dynamic
    nat-function-to-dynamic-c
    nat-function-to-dynamic-narrowing
  (id-at Nat) id★ is-just is-just
