module proof.Catchup.Core.NuImprecisionCatchupPairedFrameProof where

-- File Charter:
--   * Frames a completed weak result with one cast on each side after the
--     caller has established the final live term-imprecision relation.
--   * Is neutral among paired reveal, paired conceal, and paired widening.
--   * Contains no evidence transport, semantic dispatcher, retired
--     `PairedCast` abstraction, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyCoercion; applyTy; applyTys; keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; cast-↠)


weak-one-step-paired-frameᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A A′ B B′ c c′}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (inner : WeakOneStepResult ρ M M′ A A′ keep) →
  (resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺ (sourceResult inner ⟨
        applyCoercions (sourceChanges inner) c ⟩)
      ⊑ (targetResult inner ⟨
        applyCoercions (targetTailChanges inner)
          (applyCoercion keep c′) ⟩)
    ⦂ applyTys (sourceChanges inner) B ⊑
      applyTys (targetTailChanges inner) (applyTy keep B′)
    ∶ transportType inner q) →
  WeakOneStepResult ρ
    (M ⟨ c ⟩) (M′ ⟨ c′ ⟩) B B′ keep
weak-one-step-paired-frameᵀ
    {B = B} {B′ = B′} {c = c} {c′ = c′}
    inner final =
  record
    { sourceChanges = sourceChanges inner
    ; targetTailChanges = targetTailChanges inner
    ; sourceResult = sourceResult inner ⟨
        applyCoercions (sourceChanges inner) c ⟩
    ; targetResult = targetResult inner ⟨
        applyCoercions (targetTailChanges inner)
          (applyCoercion keep c′) ⟩
    ; resultCtx = resultCtx inner
    ; resultLeftCtx = resultLeftCtx inner
    ; resultRightCtx = resultRightCtx inner
    ; sourceCtxResult = sourceCtxResult inner
    ; targetCtxResult = targetCtxResult inner
    ; resultStore = resultStore inner
    ; resultSourceType = applyTys (sourceChanges inner) B
    ; resultTargetType =
        applyTys (targetTailChanges inner) (applyTy keep B′)
    ; sourceTypeResult = refl
    ; targetTypeResult = refl
    ; transportType = transportType inner
    ; transportAllBody = transportAllBody inner
    ; transportRightBody = transportRightBody inner
    ; transportSourceNu = transportSourceNu inner
    ; resultType = transportType inner _
    ; sourceCatchup = cast-↠ (sourceCatchup inner)
    ; targetTail = cast-↠ (targetTail inner)
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults = final
    }
