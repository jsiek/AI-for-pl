module LR-narrow.Primitive where

-- File Charter:
--   * Exposes compatibility of strict binary primitive operations.
--   * Reconciles the two CTI operand derivations at their common base type.
--   * Delegates evaluator phase decomposition to the proof namespace.

open import Data.Nat using (ℕ)

open import Types
open import Primitives
open import CastTerms
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.TermRelation
import proof.LR-narrow.Primitive as Proof

primitive-compatible : ∀ {Δᴾ Δᴵ Δᶜ}
    (op : Prim)
    {W : World Δᴾ Δᴵ Δᶜ} {Γ : CTI.CtxImp (forgetWorld W)}
    {p q : primArgTy {Δᴾ} op ⊑ᵂ⟨ core W ⟩
      primArgTy {Δᴵ} op}
    {r : primResultTy {Δᴾ} op ⊑ᵂ⟨ core W ⟩
      primResultTy {Δᴵ} op}
    {Lᴾ Mᴾ : Term Δᴾ} {Lᴵ Mᴵ : Term Δᴵ}
  → forgetWorld W ∣ Γ ⊢² Lᴾ ⊑ Lᴵ ∶ p
  → forgetWorld W ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ q
  → (∀ k → CompiledTermRelation {W = W} p k Γ Lᴾ Lᴵ)
  → (∀ k → CompiledTermRelation {W = W} q k Γ Mᴾ Mᴵ)
  → ∀ k → CompiledTermRelation {W = W} r k Γ
      (Lᴾ ⊕[ op ] Mᴾ) (Lᴵ ⊕[ op ] Mᴵ)
primitive-compatible addℕ {p = I.ι⊑ι} {q = I.ι⊑ι}
    {r = I.ι⊑ι} L⊑ M⊑ L-related M-related k =
  Proof.ForPrimitive.prim-compatible addℕ
    L⊑ M⊑ L-related M-related k
primitive-compatible and𝔹 {p = I.ι⊑ι} {q = I.ι⊑ι}
    {r = I.ι⊑ι} L⊑ M⊑ L-related M-related k =
  Proof.ForPrimitive.prim-compatible and𝔹
    L⊑ M⊑ L-related M-related k
