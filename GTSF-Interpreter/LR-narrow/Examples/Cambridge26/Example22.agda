module LR-narrow.Examples.Cambridge26.Example22 where

-- File Charter:
--   * Checks both type-imprecision derivations from Cambridge26 Example 22.
--   * These examples have no term endpoints in the note.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.CanonicalNarrowings
open import LR-narrow.Examples.Cambridge26.Specification
open import Types using (★; X₀; `∀; _⇒_)

dynamic-first : TypeExample
dynamic-first = type-example (`∀ (★ ⇒ X₀ ⇒ ★)) PolyK
  poly-k-to-dynamic-first
  poly-k-to-dynamic-first-c poly-k-to-dynamic-first-narrowing

dynamic-second : TypeExample
dynamic-second = type-example (`∀ (X₀ ⇒ ★ ⇒ X₀)) PolyK
  poly-k-to-dynamic-second
  poly-k-to-dynamic-second-c poly-k-to-dynamic-second-narrowing
