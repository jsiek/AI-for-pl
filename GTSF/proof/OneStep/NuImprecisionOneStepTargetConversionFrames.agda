module proof.OneStep.NuImprecisionOneStepTargetConversionFrames where

-- File Charter:
--   * Freezes the two outcome-level target-conversion frames needed by the
--     indexed one-step dispatcher.
--   * Each wrapper consumes an already-computed inner indexed outcome and
--     lifts only the target reduct through the ξ-⟨⟩ frame.
--   * The source term, store imprecision, and initial store change are
--     unchanged; the target coercion is transformed by that initial change.
--   * Excludes root conversion reductions; source-blame outcomes pass through
--     unchanged because the source term is not framed.

open import Conversion using (ConcealConversion; RevealConversion)
open import Data.List using (_∷_)
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyCoercion; applyTy; applyTyCtx; applyTyCtxs; applyTys)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (_⟨_⟩)
open import QuotientedTermImprecision using (⊑conv↑ᵀ; ⊑conv↓ᵀ)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import proof.Core.Properties.ReductionProperties using (applyCoercions)
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-target-cast-frameᵀ
  ; weak-one-step-target-cast-frame-transportᵀ
  ; weak-one-step-target-cast-frame-coherenceᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( apply-conceal-conversions
  ; apply-reveal-conversions
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedOutcome
  ; canonicalIndexedResults
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  ; relatedResults
  ; resultRightCtx
  ; resultStore
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )


weak-one-step-target-reveal-conversion-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ β X′ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-reveal-conversion-indexed-frame-outcomeᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ} c′↑
    (indexed-outcome-related indexed) q
    with apply-reveal-conversions
      {χs = χ ∷ targetTailChanges (weakIndexedResult indexed)} c′↑
weak-one-step-target-reveal-conversion-indexed-frame-outcomeᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ} c′↑
    (indexed-outcome-related indexed) q
    | μ′ , β′ , X′ , c′↑⁺ =
  indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed)
      framed-transport framed-coherence)
  where
  inner = weakIndexedResult indexed

  final-conversion :
    RevealConversion μ′ (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner)) β′ X′
      (applyCoercions (targetTailChanges inner) (applyCoercion χ c′))
      (applyTys (targetTailChanges inner) (applyTy χ A′))
      (applyTys (targetTailChanges inner) (applyTy χ B′))
  final-conversion =
    subst
      (λ Δ → RevealConversion μ′ Δ
        (rightStoreⁱ (resultStore inner)) β′ X′
        (applyCoercions (targetTailChanges inner) (applyCoercion χ c′))
        (applyTys (targetTailChanges inner) (applyTy χ A′))
        (applyTys (targetTailChanges inner) (applyTy χ B′)))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ′
          (applyTyCtxs (targetTailChanges inner) (applyTyCtx χ Δᴿ))
          Σ β′ X′
          (applyCoercions (targetTailChanges inner) (applyCoercion χ c′))
          (applyTys (targetTailChanges inner) (applyTy χ A′))
          (applyTys (targetTailChanges inner) (applyTy χ B′)))
        (sym (targetStoreResult inner)) c′↑⁺)

  final-relation =
    ⊑conv↑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)
  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)
weak-one-step-target-reveal-conversion-indexed-frame-outcomeᵀ
    c′↑ (indexed-outcome-source-blame source↠) q =
  indexed-outcome-source-blame source↠


weak-one-step-target-conceal-conversion-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B′ c′ μ′ β X′ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′ ⟨ applyCoercion χ c′ ⟩}
    {χ = χ} {ρ = ρ} q
weak-one-step-target-conceal-conversion-indexed-frame-outcomeᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ} c′↓
    (indexed-outcome-related indexed) q
    with apply-conceal-conversions
      {χs = χ ∷ targetTailChanges (weakIndexedResult indexed)} c′↓
weak-one-step-target-conceal-conversion-indexed-frame-outcomeᵀ
    {Δᴿ = Δᴿ} {A′ = A′} {B′ = B′} {c′ = c′} {χ = χ} c′↓
    (indexed-outcome-related indexed) q
    | μ′ , β′ , X′ , c′↓⁺ =
  indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed)
      framed-transport framed-coherence)
  where
  inner = weakIndexedResult indexed

  final-conversion :
    ConcealConversion μ′ (resultRightCtx inner)
      (rightStoreⁱ (resultStore inner)) β′ X′
      (applyCoercions (targetTailChanges inner) (applyCoercion χ c′))
      (applyTys (targetTailChanges inner) (applyTy χ A′))
      (applyTys (targetTailChanges inner) (applyTy χ B′))
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ′ Δ
        (rightStoreⁱ (resultStore inner)) β′ X′
        (applyCoercions (targetTailChanges inner) (applyCoercion χ c′))
        (applyTys (targetTailChanges inner) (applyTy χ A′))
        (applyTys (targetTailChanges inner) (applyTy χ B′)))
      (sym (targetCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ′
          (applyTyCtxs (targetTailChanges inner) (applyTyCtx χ Δᴿ))
          Σ β′ X′
          (applyCoercions (targetTailChanges inner) (applyCoercion χ c′))
          (applyTys (targetTailChanges inner) (applyTy χ A′))
          (applyTys (targetTailChanges inner) (applyTy χ B′)))
        (sym (targetStoreResult inner)) c′↓⁺)

  final-relation =
    ⊑conv↓ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  framed = weak-one-step-target-cast-frameᵀ inner final-relation
  framed-transport =
    weak-one-step-target-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)
  framed-coherence =
    weak-one-step-target-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)
weak-one-step-target-conceal-conversion-indexed-frame-outcomeᵀ
    c′↓ (indexed-outcome-source-blame source↠) q =
  indexed-outcome-source-blame source↠
