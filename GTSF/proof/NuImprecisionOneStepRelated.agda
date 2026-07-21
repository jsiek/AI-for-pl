module proof.NuImprecisionOneStepRelated where

-- File Charter:
--   * Builds the canonical keep-step result from an existing term relation.
--   * Keeps identity and terminal root proofs independent of the simulation
--     implementation module.
--   * Exports the result, transport, type-coherence, and indexed wrappers.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (keep; ↠-refl)
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuImprecisionSimulationResultDef


weak-one-step-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ M N A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ N ⦂ A ⊑ B ∶ p →
  WeakOneStepResult ρ M N A B keep
weak-one-step-relatedᵀ result =
  record
    { sourceChanges = []
    ; targetTailChanges = []
    ; sourceResult = _
    ; targetResult = _
    ; resultCtx = _
    ; resultLeftCtx = _
    ; resultRightCtx = _
    ; sourceCtxResult = refl
    ; targetCtxResult = refl
    ; resultStore = _
    ; resultSourceType = _
    ; resultTargetType = _
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = λ p → p
    ; transportAllBody = λ p → p
    ; transportRightBody = λ p → p
    ; resultType = _
    ; sourceCatchup = ↠-refl
    ; targetTail = ↠-refl
    ; sourceStoreResult = refl
    ; targetStoreResult = refl
    ; relatedResults = result
    }


weak-one-step-related-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M N A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result :
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ N ⦂ A ⊑ B ∶ p) →
  WeakOneStepTransport (weak-one-step-relatedᵀ result)
weak-one-step-related-transportᵀ result =
  weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′)


weak-one-step-related-type-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M N A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ N ⦂ A ⊑ B ∶ p) →
  WeakOneStepTypeCoherence (weak-one-step-relatedᵀ result)
weak-one-step-related-type-coherenceᵀ result =
  weak-step-type-coherence (λ pC pD → refl) (λ q → refl)


weak-one-step-indexed-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ M N A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ N ⦂ A ⊑ B ∶ p) →
  WeakOneStepIndexedResult {χ = keep} p
weak-one-step-indexed-relatedᵀ result =
  weak-indexed-result (weak-one-step-relatedᵀ result) result


weak-one-step-indexed-outcome-relatedᵀ :
  ∀ {Φ Δᴸ Δᴿ M N A B p}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ N ⦂ A ⊑ B ∶ p) →
  WeakOneStepIndexedOutcome {χ = keep} p
weak-one-step-indexed-outcome-relatedᵀ result =
  indexed-outcome-related
    (weak-one-step-indexed-relatedᵀ result)
    (weak-one-step-related-transportᵀ result)
    (weak-one-step-related-type-coherenceᵀ result)
