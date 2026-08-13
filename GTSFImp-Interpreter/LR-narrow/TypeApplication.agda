module LR-narrow.TypeApplication where

-- File Charter:
--   * Exposes compatibility of structural CTI type application.
--   * Keeps evaluator phase decomposition and world factorization private.
--   * States the theorem at the public compiled-term LR boundary.

open import Data.Nat using (ℕ; suc)

open import Types
open import CastTerms
import Consistency
import Imprecision as I
import proof.DGG.CastTermImprecision2 as CTI
open CTI using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.TermRelation
import proof.LR-narrow.TypeApplication as Proof

type-application-compatible : ∀
    {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Cᴾ : Ty (suc Δᴾ)} {Cᴵ : Ty (suc Δᴵ)}
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    {p : I.extᵐ (impEnv (core W)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W)))) Cᴾ
      ⊑ renameᵗ (extᵗ (Consistency.toRenameᵗ
        (impreciseEmbedding (core W)))) Cᴵ}
    {q : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {r : Cᴾ [ Aᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Cᴵ [ Aᴵ ]ᵗ}
    {Lᴾ : Term Δᴾ} {Lᴵ : Term Δᴵ}
  → forgetWorld W ∣ Γ ⊢² Lᴾ ⊑ Lᴵ ∶ I.∀⊑∀ p
  → (∀ k → CompiledTermRelation {W = W} (I.∀⊑∀ p) k
      Γ Lᴾ Lᴵ)
  → ∀ k → CompiledTermRelation {W = W} r k Γ
      (Lᴾ ⦂∀ Cᴾ [ Aᴾ ]) (Lᴵ ⦂∀ Cᴵ [ Aᴵ ])
type-application-compatible {q = q} =
  Proof.type-application-compatible {q = q}
