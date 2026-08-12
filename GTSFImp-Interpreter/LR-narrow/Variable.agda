module LR-narrow.Variable where

-- File Charter:
--   * Exposes variable compatibility for the open compiled-term LR.
--   * Keeps its theorem statement at the public LR boundary.
--   * Delegates the proof to proof.LR-narrow.Variable.

open import Data.Nat using (ℕ)

open import Types
open import CastTerms
import proof.DGG.CastTermImprecision2 as CTI
open import LR-narrow.World
open import LR-narrow.TermRelation
import proof.LR-narrow.Variable as Proof

variable-compatible : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)} {x} {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
  → Γ CTI.∋ʷ x ⦂ CTI.ctx-imp Aᴾ Aᴵ p
  → CompiledTermRelation {W = W} p k Γ (` x) (` x)
variable-compatible = Proof.variable-compatible
