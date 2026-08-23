module LR-narrow.TargetEvaluation where

-- File Charter:
--   * Exposes the target-store-change realization as an LR future world.
--   * Closes target phases under proof-carrying target reduction steps.
--   * Converts target phases to computations and back at precise values.
--   * Keeps the recursive StoreChanges proof in the proof namespace.

open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Types
import Imprecision as I
open import CastTerms using (Term; Value; blame)
open import Reduction using
  (StoreChange; StoreChanges; []; _∷_; _—→[_]_)
import Eval
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
import proof.LR-narrow.TargetEvaluation as Proof

target-changes-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴵ′}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → (changes : StoreChanges Δᴵ Δᴵ′)
  → TargetChangesFuture W changes
target-changes-future = Proof.target-changes-future

target-step-phase-expand : ∀ {Δᴾ Δᴵ Δᶜ Δᴵ′}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Nᴵ : Term Δᴵ′}
    {Vᴾ : Term Δᴾ} {change : StoreChange Δᴵ Δᴵ′}
  → Mᴵ ≢ blame
  → Eval.value? Mᴵ ≡ nothing
  → (step : Mᴵ —→[ change ] Nᴵ)
  → Eval.step? (impreciseStore (core W)) Mᴵ ≡
      just (Eval.step-result change Nᴵ step)
  → let first = target-changes-future W (change ∷ [])
    in TargetComputationPhase (targetWorld first)
      (λ W′ W₁≼W′ →
        R W′ (future-trans (targetFuture first) W₁≼W′))
      k Nᴵ (liftPreciseTerm (targetFuture first) Vᴾ)
  → TargetComputationPhase W R k Mᴵ Vᴾ
target-step-phase-expand = Proof.target-step-phase-expand

related-target-value-phase : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → Value Vᴵ
  → (∀ j → j ≤ k → R W future-refl j Vᴵ Vᴾ)
  → TargetComputationPhase W R k Vᴵ Vᴾ
related-target-value-phase = Proof.related-target-value-phase

future-value-computations-target-phase : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → Value Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k Mᴵ Vᴾ
  → TargetComputationPhase W (FutureValueRelation p) k Mᴵ Vᴾ
future-value-computations-target-phase =
  Proof.future-value-computations-target-phase

target-phase-computations-related : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → Value Vᴾ
  → TargetComputationPhase W R k Mᴵ Vᴾ
  → ComputationsRelated W R k Mᴵ Vᴾ
target-phase-computations-related =
  Proof.target-phase-computations-related
