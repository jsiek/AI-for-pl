module LR-narrow.Context.RightBinderRebase where

-- File Charter:
--   * Rebases a precise-right binder extension over an earlier interpretation.
--   * Preserves the chosen seal, atom, and body interpretation exactly.
--   * Contains exactly one exported theorem.

open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import Interpreter using (seal-name)
open import LR-narrow.Atoms using (_∷ᵃ_; lift-right-atoms)
open import LR-narrow.World

right-binder-rebase : ∀ {Φ Δᴸ Δᴿ current future}
    {I : Interpretation {Φ} {Δᴸ} {Δᴿ} current}
    {J : Interpretation {Φ} {Δᴸ} {Δᴿ} future}
  → J ⊒ⁱ I
  → RightBinderExtension J
  → RightBinderExtension I
right-binder-rebase J⊒I extension =
  right-binder-extension
    (right-future-world extension)
    (world-⊒-trans (right-future-extension extension) (world-future J⊒I))
    (right-binder-seal extension)
    (right-head-atom extension)
    (right-body-interpretation extension)
    (trans (right-binder-types extension)
      (cong (λ θ → seal-name (right-binder-seal extension) ∷ θ)
        (right-types-preserved J⊒I)))
    (trans (right-left-types-preserved extension)
      (left-types-preserved J⊒I))
    (trans (right-binder-atoms extension)
      (cong
        (λ ρ → right-head-atom extension ∷ᵃ lift-right-atoms ρ)
        (atoms-preserved J⊒I)))
