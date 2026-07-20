module proof.NuImprecisionOneStepSourceConversionFrames where

-- File Charter:
--   * Freezes the two outcome-level source-conversion frames needed by the
--     indexed one-step dispatcher.
--   * Each wrapper consumes an already-computed inner indexed outcome and
--     leaves the target term, target change, and store imprecision unchanged.
--   * Reveal/conceal provenance supplies the conversion evidence transported
--     across the source catch-up trace.
--   * Contains exactly the two intended hole-free leaf-proof wrappers.

open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (applyTyCtxs; applyTys)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (_⟨_⟩)
open import QuotientedTermImprecision using (conv↑⊑ᵀ; conv↓⊑ᵀ)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import proof.ReductionProperties using (applyCoercions)
open import proof.NuImprecisionSimulation using
  ( weak-one-step-source-cast-frameᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frame-coherenceᵀ
  )
open import proof.NuImprecisionSimulationCore using
  ( apply-conceal-conversions
  ; apply-reveal-conversions
  )
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedOutcome
  ; canonicalIndexedResults
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  ; relatedResults
  ; resultLeftCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  )
open import proof.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ)


weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B B′ c μ α X χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = M′} {χ = χ} {ρ = ρ} q
weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} c↑
    (indexed-outcome-related indexed transport coherence) q
    with apply-reveal-conversions
      {χs = sourceChanges (weakIndexedResult indexed)} c↑
weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} c↑
    (indexed-outcome-related indexed transport coherence) q
    | μ′ , α′ , X′ , c′↑ =
  indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed))
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation transport)
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation coherence)
  where
  inner = weakIndexedResult indexed

  final-conversion :
    RevealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner)) α′ X′
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final-conversion =
    subst
      (λ Δ → RevealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner)) α′ X′
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ α′ X′
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) c′↑)

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ
    c↑ (indexed-outcome-source-blame source↠) q =
  indexed-outcome-source-blame (cast-blame-tailᵀ source↠)


weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B B′ c μ α X χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = M′} {χ = χ} {ρ = ρ} q
weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} c↓
    (indexed-outcome-related indexed transport coherence) q
    with apply-conceal-conversions
      {χs = sourceChanges (weakIndexedResult indexed)} c↓
weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} c↓
    (indexed-outcome-related indexed transport coherence) q
    | μ′ , α′ , X′ , c′↓ =
  indexed-outcome-related
    (weak-indexed-result framed (relatedResults framed))
    (weak-one-step-source-cast-frame-transportᵀ
      inner final-relation transport)
    (weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation coherence)
  where
  inner = weakIndexedResult indexed

  final-conversion :
    ConcealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner)) α′ X′
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner)) α′ X′
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ α′ X′
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) c′↓)

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ
    c↓ (indexed-outcome-source-blame source↠) q =
  indexed-outcome-source-blame (cast-blame-tailᵀ source↠)
