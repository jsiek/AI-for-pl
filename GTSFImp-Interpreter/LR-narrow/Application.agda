module LR-narrow.Application where

-- File Charter:
--   * Exposes compatibility of the CTI application constructor.
--   * Keeps evaluator phase decomposition and world composition private.
--   * States the theorem at the public compiled-term LR boundary.

open import Data.Nat using (ℕ)

open import Types
open import CastTerms
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.TermRelation
import proof.LR-narrow.Application as Proof

application-compatible : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {Γ : CTI.CtxImp (forgetWorld W)}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ}
    {Lᴾ Mᴾ : Term Δᴾ} {Lᴵ Mᴵ : Term Δᴵ}
  → forgetWorld W ∣ Γ ⊢² Lᴾ ⊑ Lᴵ ∶ I.⇒⊑⇒ p q
  → forgetWorld W ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p
  → (∀ k → CompiledTermRelation {W = W} (I.⇒⊑⇒ p q) k
      Γ Lᴾ Lᴵ)
  → (∀ k → CompiledTermRelation {W = W} p k Γ Mᴾ Mᴵ)
  → ∀ k → CompiledTermRelation {W = W} q k Γ
      (Lᴾ · Mᴾ) (Lᴵ · Mᴵ)
application-compatible = Proof.application-compatible
