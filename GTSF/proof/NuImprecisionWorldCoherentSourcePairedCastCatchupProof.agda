module proof.NuImprecisionWorldCoherentSourcePairedCastCatchupProof where

-- File Charter:
--   * Composes accumulated-world paired-cast transport with exact-world
--     terminal paired-cast catch-up.
--   * Frames both casts without changing the final world, contexts, or
--     source/target change lists.
--   * Contains no StoreCorresponds transport or terminal cast semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyCoercion; applyTy; applyTys; keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; no•-blame
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( conv⊑convᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty)
open import proof.NuImprecisionLeftSilentPairedCastTransportDef using
  (LeftSilentPairedCastTransportᵀ)
open import proof.NuImprecisionSimulationResultDef using
  ( LeftSilentInvariant
  ; WeakOneStepResult
  ; canonicalIndexedResults
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceCatchup
  ; sourceCtxResult
  ; sourceResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; transportAllBody
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportNo•Terms
  ; transportRightBody
  ; transportType
  ; weak-indexed-result
  ; weak-step-transport
  ; weak-step-type-coherence
  ; weakIndexedResult
  )
open import proof.NuImprecisionWorldCoherentCatchupComposition using
  (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import
  proof.NuImprecisionWorldCoherentFinalPairedCastCatchupDef using
  (WorldCoherentFinalPairedCastCatchupᵀ)
open import proof.NuImprecisionWorldCoherentResultDef using
  (world-coherent-left-indexed-catchup)
open import
  proof.NuImprecisionWorldCoherentSourcePairedCastCatchupDef using
  (WorldCoherentSourcePairedCastCatchupᵀ)
open import proof.ReductionProperties using
  (applyCoercions; cast-↠)


weak-one-step-paired-cast-frameᵀ :
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
weak-one-step-paired-cast-frameᵀ
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
    ; resultType = transportType inner _
    ; sourceCatchup = cast-↠ (sourceCatchup inner)
    ; targetTail = cast-↠ (targetTail inner)
    ; sourceStoreResult = sourceStoreResult inner
    ; targetStoreResult = targetStoreResult inner
    ; relatedResults = final
    }


terminal-runtime :
  ∀ {W : Term} →
  ((Value W × No• W) ⊎ (W ≡ blame)) →
  RuntimeOK W
terminal-runtime (inj₁ (vW , noW)) = ok-no noW
terminal-runtime (inj₂ refl) = ok-no no•-blame


world-coherent-source-paired-cast-catchup-proofᵀ :
  LeftSilentPairedCastTransportᵀ →
  WorldCoherentFinalPairedCastCatchupᵀ →
  WorldCoherentSourcePairedCastCatchupᵀ
world-coherent-source-paired-cast-catchup-proofᵀ
    transport-paired final-catchup prefix paired
    vV′ noV′ inert-c′
    (world-coherent-left-indexed-catchup
      (left-indexed-catchup indexed
        (left-catchup-invariant
          silent@(left-silent-invariant refl refl) final)
        inner-transport inner-coherence)
      coherent exclusive wfL) =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    first-silent second
  where
  inner = weakIndexedResult indexed

  final-paired =
    transport-paired prefix inner silent coherent paired

  final-relation =
    conv⊑convᵀ final-paired (canonicalIndexedResults indexed)

  first = weak-one-step-paired-cast-frameᵀ inner final-relation

  first-indexed = weak-indexed-result first (relatedResults first)

  first-silent =
    left-silent-indexed
      first-indexed
      (left-silent-invariant refl refl)
      (ok-⟨⟩ (terminal-runtime final))
      (weak-step-transport
        (transportNo•Terms inner-transport))
      (weak-step-type-coherence
        (transportArrowCoherent inner-coherence)
        (transportAllCoherent inner-coherence))

  second =
    final-catchup coherent exclusive wfL final
      vV′ noV′ inert-c′ final-paired
      (canonicalIndexedResults indexed)
