module LR-narrow.Context.KripkeTrans where

-- File Charter:
--   * Proves transitivity of future interpretation extension.
--   * Composes runtime-world growth and the three preserved environments.
--   * Contains exactly one exported theorem.

open import Relation.Binary.PropositionalEquality using (trans)

open import LR-narrow.World

interpretation-⊒ⁱ-trans : ∀ {Φ Δᴸ Δᴿ w₁ w₂ w₃}
    {I₁ : Interpretation {Φ} {Δᴸ} {Δᴿ} w₁}
    {I₂ : Interpretation {Φ} {Δᴸ} {Δᴿ} w₂}
    {I₃ : Interpretation {Φ} {Δᴸ} {Δᴿ} w₃}
  → I₃ ⊒ⁱ I₂
  → I₂ ⊒ⁱ I₁
  → I₃ ⊒ⁱ I₁
interpretation-⊒ⁱ-trans I₃⊒I₂ I₂⊒I₁ =
  future-interpretation
    (world-⊒-trans (world-future I₃⊒I₂) (world-future I₂⊒I₁))
    (trans (left-types-preserved I₃⊒I₂)
      (left-types-preserved I₂⊒I₁))
    (trans (right-types-preserved I₃⊒I₂)
      (right-types-preserved I₂⊒I₁))
    (trans (atoms-preserved I₃⊒I₂) (atoms-preserved I₂⊒I₁))
