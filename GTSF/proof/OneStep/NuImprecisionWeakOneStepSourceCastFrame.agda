module proof.OneStep.NuImprecisionWeakOneStepSourceCastFrame where

-- File Charter:
--   * Frames a generic weak one-step result with one source cast.
--   * Preserves the silent, transport, and type-coherence invariants exposed
--     by the inner result.
--   * Contains no cast-shape analysis, semantic cast case, or dispatcher.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (applyTy; applyTys; keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp)
open import NuTerms using (_⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; cast-↠)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftSilentInvariant
  ; WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceCatchup
  ; sourceChanges
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; transportAllBody
  ; transportAllBodyPairedReplacementCoherent
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportLeftReplacementCoherent
  ; transportNo•Terms
  ; transportPairedReplacementCoherent
  ; transportRightBody
  ; transportRightBodyRightReplacementCoherent
  ; transportRightBodyShapeCoherent
  ; transportRightReplacementCoherent
  ; transportShapeCoherent
  ; transportSourceNu
  ; transportSourceNuBodyLeftReplacementCoherent
  ; transportType
  ; weak-step-transport
  ; weak-step-type-coherence
  )


weak-one-step-source-cast-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ M N′ A A′ χ) →
  (resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ (sourceResult inner ⟨ applyCoercions (sourceChanges inner) c ⟩)
      ⊑ targetResult inner
    ⦂ applyTys (sourceChanges inner) B
      ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
    ∶ transportType inner q) →
  WeakOneStepResult ρ (M ⟨ c ⟩) N′ B B′ χ
weak-one-step-source-cast-frameᵀ
    {B = B} {B′ = B′} {c = c} {χ = χ} inner result =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult =
        sourceResult inner ⟨ applyCoercions (sourceChanges inner) c ⟩
    ; targetResult = targetResult inner
    ; resultCtx = resultCtx inner
    ; resultLeftCtx = resultLeftCtx inner
    ; resultRightCtx = resultRightCtx inner
    ; sourceCtxResult = sourceCtxResult inner
    ; targetCtxResult = targetCtxResult inner
    ; resultStore = resultStore inner
    ; resultSourceType = applyTys (sourceChanges inner) B
    ; resultTargetType =
        applyTys (targetTailChanges inner) (applyTy χ B′)
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = transportType inner
    ; transportAllBody = transportAllBody inner
    ; transportRightBody = transportRightBody inner
    ; transportSourceNu = transportSourceNu inner
    ; resultType = transportType inner _
    ; sourceCatchup = cast-↠ (sourceCatchup inner)
    ; targetTail = targetTail inner
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults = result
    }


weak-one-step-source-cast-frame-silentᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B B′ c}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M N′ A A′ keep)
    (result : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ (sourceResult inner ⟨
          applyCoercions (sourceChanges inner) c ⟩)
        ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy keep B′)
      ∶ transportType inner q) →
  LeftSilentInvariant inner →
  LeftSilentInvariant
    (weak-one-step-source-cast-frameᵀ inner result)
weak-one-step-source-cast-frame-silentᵀ
    inner result (left-silent-invariant refl refl) =
  left-silent-invariant refl refl


weak-one-step-source-cast-frame-transportᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M N′ A A′ χ)
    (result : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ (sourceResult inner ⟨ applyCoercions (sourceChanges inner) c ⟩)
        ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner q) →
  WeakOneStepTransport inner →
  WeakOneStepTransport
    (weak-one-step-source-cast-frameᵀ inner result)
weak-one-step-source-cast-frame-transportᵀ
    inner result transport =
  weak-step-transport (transportNo•Terms transport)


weak-one-step-source-cast-frame-coherenceᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B B′ c χ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (inner : WeakOneStepResult ρ M N′ A A′ χ)
    (result : resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ (sourceResult inner ⟨ applyCoercions (sourceChanges inner) c ⟩)
        ⊑ targetResult inner
      ⦂ applyTys (sourceChanges inner) B
        ⊑ applyTys (targetTailChanges inner) (applyTy χ B′)
      ∶ transportType inner q) →
  WeakOneStepTypeCoherence inner →
  WeakOneStepTypeCoherence
    (weak-one-step-source-cast-frameᵀ inner result)
weak-one-step-source-cast-frame-coherenceᵀ
    inner result coherence =
  weak-step-type-coherence
    (transportArrowCoherent coherence)
    (transportAllCoherent coherence)
    (transportShapeCoherent coherence)
    (transportRightBodyShapeCoherent coherence)
    (transportLeftReplacementCoherent coherence)
    (transportRightReplacementCoherent coherence)
    (transportPairedReplacementCoherent coherence)
    (transportAllBodyPairedReplacementCoherent coherence)
    (transportSourceNuBodyLeftReplacementCoherent coherence)
    (transportRightBodyRightReplacementCoherent coherence)
