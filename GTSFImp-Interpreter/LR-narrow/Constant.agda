module LR-narrow.Constant where

-- File Charter:
--   * Exposes compatibility of identical constants in the open compiled LR.
--   * Keeps the theorem statement at the public LR boundary.
--   * Delegates the proof to proof.LR-narrow.Constant.

open import Data.Nat using (ℕ)

open import Types
open import Primitives
open import CastTerms
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open import LR-narrow.World
open import LR-narrow.TermRelation
import proof.LR-narrow.Constant as Proof

constant-compatible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)} (κ : Const)
    {p : constTy {Δᴾ} κ ⊑ᵂ⟨ core W ⟩ constTy {Δᴵ} κ}
  → CompiledTermRelation {W = W} p k Γ ($ κ) ($ κ)
constant-compatible = Proof.constant-compatible
