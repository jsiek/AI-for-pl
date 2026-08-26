module LR-narrow.Context.TermRelation where

-- File Charter:
--   * Defines the open interpreter-computation judgment used by context
--     compatibility lemmas.
--   * Orders environments and terms as imprecise-left, precise-right.
--   * Fixes the concrete term and type environments through an LR
--     interpretation.
--   * Contains no compatibility theorem or small-step dependency.

open import Data.Nat using (ℕ)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter using (Environment; interpret)
open import LR-narrow.LogicalRelation using
  (ComputationsRelated; ValueNarrowing)
open import LR-narrow.World using
  ( Interpretation
  ; World
  ; left-types
  ; left-world
  ; right-types
  ; right-world
  )
open import NuTerms using (Term)
open import Types using (Ty; TyCtx)

TermRelation : ∀ {Φ : ImpCtx} {Δᴾ Δᴵ : TyCtx} {Aᴾ Aᴵ : Ty}
  → (p : Φ ∣ Δᴾ ⊢ Aᴾ ⊑ Aᴵ ⊣ Δᴵ)
  → {w : World}
  → Interpretation {Φ} {Δᴾ} {Δᴵ} w
  → ℕ
  → Environment → Environment
  → Term → Term
  → Set₁
TermRelation p {w} I k γᴵ γᴾ Mᴵ Mᴾ =
  ComputationsRelated (ValueNarrowing p) I k
    (λ n → interpret (left-world w) γᴵ (left-types I) Mᴵ n)
    (λ n → interpret (right-world w) γᴾ (right-types I) Mᴾ n)
