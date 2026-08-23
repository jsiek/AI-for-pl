module LR-narrow.Blame where

-- File Charter:
--   * Exposes open-term compatibility of the CTI precise-blame constructor.
--   * Delegates evaluator reasoning to the proof namespace.

open import Data.Nat using (ℕ)

open import Types
open import CastTerms
import proof.DGG.CtxImp as CTI
open import LR-narrow.World
open import LR-narrow.TermRelation
import proof.LR-narrow.Blame as Proof

blame-compatible : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)} {Mᴵ : Term Δᴵ}
  → ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) , CTI.tgtCtxʷ Γ ⟩
      ⊢ Mᴵ ⦂ Aᴵ
  → (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
  → CompiledTermRelation {W = W} p k Γ blame Mᴵ
blame-compatible Mᴵ⊢ p = Proof.blame-compatible p
