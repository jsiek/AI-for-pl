module LR-narrow.Context.PairedBinderRebase where

-- File Charter:
--   * Rebases a paired binder extension over an earlier interpretation.
--   * Preserves the chosen seals, atom, and body interpretation exactly.
--   * Contains exactly one exported theorem.

open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import Interpreter using (seal-name)
open import LR-narrow.Atoms using (_∷ᵃ_; lift-both-atoms)
open import LR-narrow.World

paired-binder-rebase : ∀ {Φ Δᴸ Δᴿ current future}
    {I : Interpretation {Φ} {Δᴸ} {Δᴿ} current}
    {J : Interpretation {Φ} {Δᴸ} {Δᴿ} future}
  → J ⊒ⁱ I
  → PairedBinderExtension J
  → PairedBinderExtension I
paired-binder-rebase J⊒I extension =
  paired-binder-extension
    (paired-future extension)
    (world-⊒-trans (paired-future-world extension) (world-future J⊒I))
    (paired-left-seal extension)
    (paired-right-seal extension)
    (λ binding → paired-left-fresh extension
      (paired-binding-weaken
        (bindings-future (world-future J⊒I)) binding))
    (λ binding → paired-right-fresh extension
      (paired-binding-weaken
        (bindings-future (world-future J⊒I)) binding))
    (paired-head-atom extension)
    (paired-body-interpretation extension)
    (trans (paired-left-types extension)
      (cong (λ θ → seal-name (paired-left-seal extension) ∷ θ)
        (left-types-preserved J⊒I)))
    (trans (paired-right-types extension)
      (cong (λ θ → seal-name (paired-right-seal extension) ∷ θ)
        (right-types-preserved J⊒I)))
    (trans (paired-atoms extension)
      (cong
        (λ ρ → paired-head-atom extension ∷ᵃ lift-both-atoms ρ)
        (atoms-preserved J⊒I)))
