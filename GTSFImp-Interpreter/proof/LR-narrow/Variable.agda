module proof.LR-narrow.Variable where

-- File Charter:
--   * Proves compatibility of corresponding variables in the open LR.
--   * Obtains the related closed values from related-substitution lookup.
--   * Delegates all evaluator reasoning to the immediate-return theorem.

open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (≤-refl)

open import Types
open import CastTerms
import proof.DGG.CastTermImprecision2 as CTI
open import LR-narrow.World
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation
open import LR-narrow.ImmediateReturn

variable-compatible : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)} {x} {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
  → Γ CTI.∋ʷ x ⦂ CTI.ctx-imp Aᴾ Aᴵ p
  → CompiledTermRelation {W = W} p k Γ (` x) (` x)
variable-compatible {W = W} {k = k} {x = x} {p = p} x∈ W′ W≼W′ γ
    rewrite liftImpreciseTerm-variable W≼W′ x
          | liftPreciseTerm-variable W≼W′ x =
  related-values-return (imprecise-value endpoints)
    (precise-value endpoints) related
  where
  local = related-closing-lookup
    (lift-context-lookup W≼W′ (compiled-context-lookup x∈)) γ
  related = λ j j≤k → value-imprecision-local→center W≼W′ p
    (local j j≤k)
  endpoints = value-imprecision-endpoints (related k ≤-refl)
