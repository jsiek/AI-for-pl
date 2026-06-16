-- File Charter:
--   * Blame labels represented as nonempty lists of natural-number positions.
--   * Primary exports are `Label` and `push`.
--   * Depends only on natural numbers and nonempty lists from the standard
--     library.

module Label where

open import Data.Nat using (ℕ)
open import Data.List.NonEmpty using (List⁺; _∷⁺_)

Label = List⁺ ℕ

push : ℕ → Label → Label
push = _∷⁺_
