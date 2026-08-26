module LR-narrow.Context.RelatedEnvironments where

-- File Charter:
--   * Defines term environments related pointwise by their live context-
--     imprecision entries.
--   * Stores the imprecise environment first and precise environment second.
--   * Retains relation evidence at every index up to the current observation
--     budget so lookup directly supplies residual-fuel evidence.
--   * Contains no lookup or compatibility theorem.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _≤_)

open import Interpreter using (Environment; Value)
open import LR-narrow.LogicalRelation using (ValueNarrowing)
open import LR-narrow.World using (Interpretation; World)
open import proof.NuCore.Relations.NuImprecisionTermContextDef
  using (CtxImp; ctx-imp)
open import Types using (TyCtx)

data RelatedEnvironments
    {Φ} {Δᴾ Δᴵ : TyCtx} {w : World}
    (I : Interpretation {Φ} {Δᴾ} {Δᴵ} w) (k : ℕ) :
    CtxImp Φ Δᴾ Δᴵ → Environment → Environment → Set₁ where
  related-empty :
    RelatedEnvironments I k [] [] []

  related-cons : ∀ {Γ γᴵ γᴾ Aᴾ Aᴵ p Vᴵ Vᴾ}
    → (∀ j → j ≤ k → ValueNarrowing p I j Vᴵ Vᴾ)
    → RelatedEnvironments I k Γ γᴵ γᴾ
    → RelatedEnvironments I k
        (ctx-imp Aᴾ Aᴵ p ∷ Γ) (Vᴵ ∷ γᴵ) (Vᴾ ∷ γᴾ)
