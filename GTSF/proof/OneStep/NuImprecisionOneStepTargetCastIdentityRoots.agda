module proof.OneStep.NuImprecisionOneStepTargetCastIdentityRoots where

-- File Charter:
--   * Proves target-side β-id root outcomes for ordinary narrowing and
--     widening casts.
--   * Retains the dispatcher-supplied desired result index q instead of
--     appealing to proof irrelevance.
--   * Inverts the identity-coercion narrowing/widening judgment to recover
--     the atomic target shape, then reindexes the related target value.
--   * Supplies the strict helper lemmas for the target-cast root dispatcher.

import Coercions as C
open import Coercions using (id-onlyᵈ)
open import Data.List using ([])
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
import NarrowWiden as NW
open import NuReduction using (keep)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (＇_; ‵_; ★)
open import proof.OneStep.NuImprecisionAtomicTargetReindex using
  (atomic-target-value-reindexᵀ)
open import proof.OneStep.NuImprecisionOneStepRelated using
  (weak-one-step-indexed-outcome-relatedᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  (WeakOneStepIndexedOutcome)


weak-one-step-target-narrow-cast-identity-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M V A A′ B′ I μ′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ C.id I ∶ A′ ⊒ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  Value V →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = V} {χ = keep} {ρ = ρ} q
weak-one-step-target-narrow-cast-identity-root-outcomeᵀ
    (C.cast-id _ _ , NW.cross (NW.id-＇ α)) M⊑V q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (atomic-target-value-reindexᵀ (＇ α) vV M⊑V q)
weak-one-step-target-narrow-cast-identity-root-outcomeᵀ
    (C.cast-id _ _ , NW.cross (NW.id-‵ ι)) M⊑V q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (atomic-target-value-reindexᵀ (‵ ι) vV M⊑V q)
weak-one-step-target-narrow-cast-identity-root-outcomeᵀ
    (C.cast-id _ _ , NW.id★) M⊑V q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (atomic-target-value-reindexᵀ ★ vV M⊑V q)


weak-one-step-target-widen-cast-identity-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M V A A′ B′ I μ′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ C.id I ∶ A′ ⊑ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  Value V →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = V} {χ = keep} {ρ = ρ} q
weak-one-step-target-widen-cast-identity-root-outcomeᵀ
    (C.cast-id _ _ , NW.cross (NW.id-＇ α)) M⊑V q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (atomic-target-value-reindexᵀ (＇ α) vV M⊑V q)
weak-one-step-target-widen-cast-identity-root-outcomeᵀ
    (C.cast-id _ _ , NW.cross (NW.id-‵ ι)) M⊑V q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (atomic-target-value-reindexᵀ (‵ ι) vV M⊑V q)
weak-one-step-target-widen-cast-identity-root-outcomeᵀ
    (C.cast-id _ _ , NW.id★) M⊑V q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (atomic-target-value-reindexᵀ ★ vV M⊑V q)


weak-one-step-target-widen-id-cast-identity-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M V A A′ B′ I}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ C.id I ∶ A′ ⊑ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  Value V →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = V} {χ = keep} {ρ = ρ} q
weak-one-step-target-widen-id-cast-identity-root-outcomeᵀ
    (C.cast-id _ _ , NW.cross (NW.id-＇ α)) M⊑V q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (atomic-target-value-reindexᵀ (＇ α) vV M⊑V q)
weak-one-step-target-widen-id-cast-identity-root-outcomeᵀ
    (C.cast-id _ _ , NW.cross (NW.id-‵ ι)) M⊑V q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (atomic-target-value-reindexᵀ (‵ ι) vV M⊑V q)
weak-one-step-target-widen-id-cast-identity-root-outcomeᵀ
    (C.cast-id _ _ , NW.id★) M⊑V q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (atomic-target-value-reindexᵀ ★ vV M⊑V q)
