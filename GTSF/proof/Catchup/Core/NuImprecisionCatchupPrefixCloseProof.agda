module proof.Catchup.Core.NuImprecisionCatchupPrefixCloseProof where

-- File Charter:
--   * Proves live quotient closing by transporting the outer widening and
--     compatibility evidence through one completed left-silent catch-up.
--   * Frames the already-transported paired narrowing and reconstructs one
--     `closeᵀ` result without invoking quotient terminal semantics.
--   * Contains no recursive dispatcher, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyTy; applyTys; keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp)
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; blame
  ; no•-blame
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  (closeᵀ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import
  proof.Catchup.Core.NuImprecisionCatchupPrefixCloseDef
  using (LeftSilentIndexedPrefixCloseᵀ)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (cast-shape-applyCoercions)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using (weak-one-step-transport-quotient-boundary-square)
open import
  proof.OneStep.NuImprecisionWeakOneStepQuotientCompatibilityTransport
  using
  (weak-one-step-transport-quotient-widening-compatibleᵀ)
open import proof.Quotient.NuImprecisionQuotientWideningTransport using
  (weak-one-step-transport-quotient-widening-pairᵀ)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; cast-↠)


private
  left-catchup-final-runtime :
    ∀ {Φ Δᴸ Δᴿ M V′ A B}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {result : WeakOneStepResult ρ M V′ A B keep} →
    LeftCatchupInvariant result →
    RuntimeOK (sourceResult result)
  left-catchup-final-runtime
      (left-catchup-invariant silent (inj₁ (vV , noV))) =
    ok-no noV
  left-catchup-final-runtime
      (left-catchup-invariant silent (inj₂ refl)) =
    ok-no no•-blame


  weak-one-step-close-frameᵀ :
    ∀ {Φ Δᴸ Δᴿ M M′ C C′ A A′ d d′ u u′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ} →
    (inner : WeakOneStepResult ρ M M′ C C′ keep) →
    LeftSilentInvariant inner →
    (resultCtx inner
      ∣ resultLeftCtx inner
      ∣ resultRightCtx inner
      ∣ resultStore inner ∣ []
      ⊢ᴺ ((sourceResult inner ⟨
            applyCoercions (sourceChanges inner) d ⟩) ⟨
          applyCoercions (sourceChanges inner) u ⟩)
        ⊑ ((targetResult inner ⟨ d′ ⟩) ⟨ u′ ⟩)
      ⦂ applyTys (sourceChanges inner) A ⊑
          applyTys (targetTailChanges inner) (applyTy keep A′)
      ∶ transportType inner pA) →
    WeakOneStepResult ρ
      ((M ⟨ d ⟩) ⟨ u ⟩) ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩)
      A A′ keep
  weak-one-step-close-frameᵀ
      {A = A} {A′ = A′}
      {d = d} {d′ = d′} {u = u} {u′ = u′}
      inner (left-silent-invariant refl refl) final =
    record
      { sourceChanges = sourceChanges inner
      ; targetTailChanges = []
      ; sourceResult = (sourceResult inner ⟨
          applyCoercions (sourceChanges inner) d ⟩) ⟨
            applyCoercions (sourceChanges inner) u ⟩
      ; targetResult = (targetResult inner ⟨ d′ ⟩) ⟨ u′ ⟩
      ; resultCtx = resultCtx inner
      ; resultLeftCtx = resultLeftCtx inner
      ; resultRightCtx = resultRightCtx inner
      ; sourceCtxResult = sourceCtxResult inner
      ; targetCtxResult = targetCtxResult inner
      ; resultStore = resultStore inner
      ; resultSourceType = applyTys (sourceChanges inner) A
      ; resultTargetType = A′
      ; sourceTypeResult = refl
      ; targetTypeResult = refl
      ; transportType = transportType inner
      ; transportAllBody = transportAllBody inner
      ; transportRightBody = transportRightBody inner
      ; transportSourceNu = transportSourceNu inner
      ; resultType = transportType inner _
      ; sourceCatchup = cast-↠ (cast-↠ (sourceCatchup inner))
      ; targetTail = cast-↠ (cast-↠ (targetTail inner))
      ; sourceStoreResult = sourceStoreResult inner
      ; targetStoreResult = targetStoreResult inner
      ; relatedResults = final
      }


left-silent-indexed-prefix-close-proofᵀ :
  LeftSilentIndexedPrefixCloseᵀ
left-silent-indexed-prefix-close-proofᵀ
    {pA = pA} prefix widening-pair u-shape u′-shape square compatible
    (left-indexed-catchup indexed
      invariant@(left-catchup-invariant
        silent@(left-silent-invariant refl refl) final))
    final-unique down =
  left-silent-indexed
    (weak-indexed-result framed final-relation
      (weak-step-transport
        (transportNo•Terms (weakIndexedTransport indexed)))
      (weak-step-type-coherence
        (transportArrowCoherent (weakIndexedTypeCoherence indexed))
        (transportAllCoherent (weakIndexedTypeCoherence indexed))
        (transportShapeCoherent (weakIndexedTypeCoherence indexed))
        (transportRightBodyShapeCoherent
          (weakIndexedTypeCoherence indexed))
        (transportLeftReplacementCoherent
          (weakIndexedTypeCoherence indexed))
        (transportRightReplacementCoherent
          (weakIndexedTypeCoherence indexed))
        (transportPairedReplacementCoherent
          (weakIndexedTypeCoherence indexed))
        (transportAllBodyPairedReplacementCoherent
          (weakIndexedTypeCoherence indexed))
        (transportSourceNuBodyLeftReplacementCoherent
          (weakIndexedTypeCoherence indexed))
        (transportRightBodyRightReplacementCoherent
          (weakIndexedTypeCoherence indexed))))
    (left-silent-invariant refl refl)
    (ok-⟨⟩ (ok-⟨⟩ (left-catchup-final-runtime invariant)))
  where
  inner = weakIndexedResult indexed

  final-widening =
    weak-one-step-transport-quotient-widening-pairᵀ
      prefix inner silent widening-pair

  final-compatible =
    weak-one-step-transport-quotient-widening-compatibleᵀ
      inner (weakIndexedTypeCoherence indexed) final-unique compatible

  final-relation =
    closeᵀ down final-widening (transportType inner pA)
      (cast-shape-applyCoercions
        (sourceChanges inner) u-shape)
      u′-shape
      (weak-one-step-transport-quotient-boundary-square
        inner (weakIndexedTypeCoherence indexed) square)
      final-compatible

  framed = weak-one-step-close-frameᵀ inner silent final-relation
