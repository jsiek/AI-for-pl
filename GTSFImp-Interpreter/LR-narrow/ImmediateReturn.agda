module LR-narrow.ImmediateReturn where

-- File Charter:
--   * Exposes the immediate-return theorem for evaluator values.
--   * Exposes the generic lift from pointwise related values to related
--     computations.
--   * Delegates evaluator-specific proof scripts to the proof namespace.

open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TyStore
open import CastTerms
open import Reduction using ([]; ↠-refl)
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
import proof.LR-narrow.ImmediateReturn as Proof

value-return : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
  → (gas : ℕ)
  → Value V
  → Σ[ vV ∈ Value V ]
      interpretFrom Σ gas V
        ≡ returned (E.result Δ [] V ↠-refl vV)
value-return {Σ = Σ} = Proof.value-return {Σ = Σ}

related-values-return : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → Value Vᴵ
  → Value Vᴾ
  → (∀ j → j ≤ k → R W future-refl j Vᴵ Vᴾ)
  → ComputationsRelated W R k Vᴵ Vᴾ
related-values-return = Proof.related-values-return
