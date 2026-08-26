module LR-narrow.Context.RelatedEnvironmentLookup where

-- File Charter:
--   * Looks up both semantic values represented by one context-imprecision
--     membership proof.
--   * Returns the imprecise-left value before the precise-right value.
--   * Returns their exact environment equations and LR evidence at every
--     smaller observation index.
--   * Contains exactly one exported theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_×_; Σ-syntax; _,_)

open import Interpreter using (Environment; Value; lookup)
open import LR-narrow.Context.RelatedEnvironments
open import LR-narrow.LogicalRelation using (ValueNarrowing)
open import LR-narrow.World using (Interpretation; World)
open import proof.NuCore.Relations.NuImprecisionTermContextDef
  using (CtxImp; ctx-imp)
open import Types using (TyCtx; _∋_⦂_; Z; S)

related-environment-lookup : ∀
    {Φ} {Δᴾ Δᴵ : TyCtx} {w : World}
    {I : Interpretation {Φ} {Δᴾ} {Δᴵ} w} {k : ℕ}
    {Γ : CtxImp Φ Δᴾ Δᴵ} {γᴵ γᴾ : Environment}
    {x Aᴾ Aᴵ p}
  → Γ ∋ x ⦂ ctx-imp Aᴾ Aᴵ p
  → RelatedEnvironments I k Γ γᴵ γᴾ
  → Σ[ Vᴵ ∈ Value ] Σ[ Vᴾ ∈ Value ]
      (lookup γᴵ x ≡ just Vᴵ) ×
      (lookup γᴾ x ≡ just Vᴾ) ×
      (∀ j → j ≤ k → ValueNarrowing p I j Vᴵ Vᴾ)
related-environment-lookup Z
    (related-cons related rest) =
  _ , _ , refl , refl , related
related-environment-lookup (S x∈)
    (related-cons related rest) =
  related-environment-lookup x∈ rest
