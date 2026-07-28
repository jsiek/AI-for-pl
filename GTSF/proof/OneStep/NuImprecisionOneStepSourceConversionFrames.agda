module proof.OneStep.NuImprecisionOneStepSourceConversionFrames where

-- File Charter:
--   * Freezes the two outcome-level source-conversion frames needed by the
--     indexed one-step dispatcher.
--   * Each wrapper consumes an already-computed inner indexed outcome and
--     leaves the target term, target change, and store imprecision unchanged.
--   * Reveal/conceal provenance supplies the conversion evidence transported
--     across the source catch-up trace.
--   * Contains exactly the two intended hole-free leaf-proof wrappers.

open import Conversion using (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴸ_)
open import Data.Product using (_,_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (applyTyCtxs; applyTys)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using (_⟨_⟩)
open import QuotientedTermImprecision using (conv↑⊑ᵀ; conv↓⊑ᵀ)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyTyVars)
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-source-cast-frameᵀ
  ; weak-one-step-source-cast-frame-transportᵀ
  ; weak-one-step-source-cast-frame-coherenceᵀ
  )
open import proof.Core.Properties.NuConversionTransport
  using
  ( apply-conceal-conversions-exact
  ; apply-reveal-conversions-exact
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedOutcome
  ; WeakOneStepIndexedResult
  ; canonicalIndexedResults
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  ; relatedResults
  ; resultLeftCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; transportLeftReplacementCoherent
  ; transportType
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ)


weak-one-step-source-reveal-conversion-indexed-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B B′ c μ α X χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WeakOneStepIndexedResult
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  p [ α ↦ X ]ᴸ q →
  WeakOneStepIndexedResult
    {M = M ⟨ c ⟩} {N′ = M′} {χ = χ} {ρ = ρ} q
weak-one-step-source-reveal-conversion-indexed-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {α = α} {X = X}
    c↑ indexed q replace
    with apply-reveal-conversions-exact
      {χs = sourceChanges (weakIndexedResult indexed)} c↑
weak-one-step-source-reveal-conversion-indexed-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {α = α} {X = X}
    c↑ indexed q replace
    | μ′ , c′↑ =
  weak-indexed-result framed (relatedResults framed)
    framed-transport framed-coherence
  where
  inner = weakIndexedResult indexed

  final-conversion :
    RevealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner))
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final-conversion =
    subst
      (λ Δ → RevealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner))
        (applyTyVars (sourceChanges inner) α)
        (applyTys (sourceChanges inner) X)
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → RevealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ
          (applyTyVars (sourceChanges inner) α)
          (applyTys (sourceChanges inner) X)
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) c′↑)

  final-relation =
    conv↑⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed) replace)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)
  framed-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)


weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B B′ c μ α X χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  p [ α ↦ X ]ᴸ q →
  WeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = M′} {χ = χ} {ρ = ρ} q
weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ
    c↑ (indexed-outcome-related indexed) q replace =
  indexed-outcome-related
    (weak-one-step-source-reveal-conversion-indexed-frameᵀ
      c↑ indexed q replace)
weak-one-step-source-reveal-conversion-indexed-frame-outcomeᵀ
    c↑ (indexed-outcome-source-blame source↠) q replace =
  indexed-outcome-source-blame (cast-blame-tailᵀ source↠)


weak-one-step-source-conceal-conversion-indexed-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B B′ c μ α X χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WeakOneStepIndexedResult
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  q [ α ↦ X ]ᴸ p →
  WeakOneStepIndexedResult
    {M = M ⟨ c ⟩} {N′ = M′} {χ = χ} {ρ = ρ} q
weak-one-step-source-conceal-conversion-indexed-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {α = α} {X = X}
    c↓ indexed q replace
    with apply-conceal-conversions-exact
      {χs = sourceChanges (weakIndexedResult indexed)} c↓
weak-one-step-source-conceal-conversion-indexed-frameᵀ
    {Δᴸ = Δᴸ} {A = A} {B = B} {c = c} {α = α} {X = X}
    c↓ indexed q replace
    | μ′ , c′↓ =
  weak-indexed-result framed (relatedResults framed)
    framed-transport framed-coherence
  where
  inner = weakIndexedResult indexed

  final-conversion :
    ConcealConversion μ′ (resultLeftCtx inner)
      (leftStoreⁱ (resultStore inner))
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyCoercions (sourceChanges inner) c)
      (applyTys (sourceChanges inner) A)
      (applyTys (sourceChanges inner) B)
  final-conversion =
    subst
      (λ Δ → ConcealConversion μ′ Δ
        (leftStoreⁱ (resultStore inner))
        (applyTyVars (sourceChanges inner) α)
        (applyTys (sourceChanges inner) X)
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B))
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → ConcealConversion μ′
          (applyTyCtxs (sourceChanges inner) Δᴸ) Σ
          (applyTyVars (sourceChanges inner) α)
          (applyTys (sourceChanges inner) X)
          (applyCoercions (sourceChanges inner) c)
          (applyTys (sourceChanges inner) A)
          (applyTys (sourceChanges inner) B))
        (sym (sourceStoreResult inner)) c′↓)

  final-relation =
    conv↓⊑ᵀ final-conversion
      (canonicalIndexedResults indexed) (transportType inner q)
      (transportLeftReplacementCoherent
        (weakIndexedTypeCoherence indexed) replace)

  framed = weak-one-step-source-cast-frameᵀ inner final-relation
  framed-transport =
    weak-one-step-source-cast-frame-transportᵀ
      inner final-relation (weakIndexedTransport indexed)
  framed-coherence =
    weak-one-step-source-cast-frame-coherenceᵀ
      inner final-relation (weakIndexedTypeCoherence indexed)


weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B B′ c μ α X χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = M′} {χ = χ} {ρ = ρ} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  q [ α ↦ X ]ᴸ p →
  WeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = M′} {χ = χ} {ρ = ρ} q
weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ
    c↓ (indexed-outcome-related indexed) q replace =
  indexed-outcome-related
    (weak-one-step-source-conceal-conversion-indexed-frameᵀ
      c↓ indexed q replace)
weak-one-step-source-conceal-conversion-indexed-frame-outcomeᵀ
    c↓ (indexed-outcome-source-blame source↠) q replace =
  indexed-outcome-source-blame (cast-blame-tailᵀ source↠)
