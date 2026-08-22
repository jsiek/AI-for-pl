module LR-narrow.BetaExpansion where

-- File Charter:
--   * Exposes closure of related computations under matching beta expansion.
--   * Accounts for the one LR index consumed by the two beta steps.
--   * Delegates evaluator inversion and trace construction to the proof module.

open import Data.Nat using (ℕ; suc)

open import Types
open import CastTerms
open import LR-narrow.World
open import LR-narrow.Computation
import proof.LR-narrow.BetaExpansion as Proof

related-beta-expand : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Nᴵ Vᴵ : Term Δᴵ} {Nᴾ Vᴾ : Term Δᴾ}
  → Value Vᴵ
  → Value Vᴾ
  → ComputationsRelated W R k (Nᴵ [ Vᴵ ]) (Nᴾ [ Vᴾ ])
  → ComputationsRelated W R (suc k)
      ((ƛ Nᴵ) · Vᴵ) ((ƛ Nᴾ) · Vᴾ)
related-beta-expand = Proof.related-beta-expand
