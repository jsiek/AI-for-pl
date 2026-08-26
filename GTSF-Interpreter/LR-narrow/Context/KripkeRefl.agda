module LR-narrow.Context.KripkeRefl where

-- File Charter:
--   * Proves reflexivity of future interpretation extension.
--   * Supplies the common-world witness used by immediate-return context
--     lemmas.
--   * Contains exactly one exported theorem.

open import Agda.Builtin.Equality using (refl)

open import LR-narrow.World

interpretation-⊒ⁱ-refl : ∀ {Φ Δᴸ Δᴿ w}
  → (I : Interpretation {Φ} {Δᴸ} {Δᴿ} w)
  → I ⊒ⁱ I
interpretation-⊒ⁱ-refl I =
  future-interpretation world-⊒-refl refl refl refl
