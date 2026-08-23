module LR-narrow.TargetEvaluation where

-- File Charter:
--   * Exposes the target-store-change realization as an LR future world.
--   * Exposes conversion of a completed target phase to related computations.
--   * Keeps the recursive StoreChanges proof in the proof namespace.

open import Data.Nat using (ℕ)
open import Types
open import CastTerms using (Term; Value)
open import Reduction using (StoreChanges)
open import LR-narrow.World
open import LR-narrow.Computation
import proof.LR-narrow.TargetEvaluation as Proof

target-changes-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴵ′}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → (changes : StoreChanges Δᴵ Δᴵ′)
  → TargetChangesFuture W changes
target-changes-future = Proof.target-changes-future

target-phase-computations-related : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → Value Vᴾ
  → TargetComputationPhase W R k Mᴵ Vᴾ
  → ComputationsRelated W R k Mᴵ Vᴾ
target-phase-computations-related =
  Proof.target-phase-computations-related
