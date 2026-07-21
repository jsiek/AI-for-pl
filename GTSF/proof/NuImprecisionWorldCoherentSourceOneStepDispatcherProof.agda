module proof.NuImprecisionWorldCoherentSourceOneStepDispatcherProof where

-- File Charter:
--   * Proves that the nine frozen source-reduction case capabilities assemble
--     into the ambient-prefix exact source one-step dispatcher.
--   * Splits exhaustively on the source store-step derivation.
--   * Contains no semantic case implementation, postulate, or hole.

open import NuReduction using
  ( blame-ν
  ; pure-step
  ; ν-step
  ; ξ-·₁
  ; ξ-·₂
  ; ξ-⟨⟩
  ; ξ-ν
  ; ξ-⊕₁
  ; ξ-⊕₂
  )
open import proof.NuImprecisionWorldCoherentSourceOneStepCasesDef using
  ( WorldCoherentSourceOneStepCases
  ; sourceAllocationStepCase
  ; sourceApplicationLeftStepCase
  ; sourceApplicationRightStepCase
  ; sourceCastFrameStepCase
  ; sourceNuBlameStepCase
  ; sourceNuFrameStepCase
  ; sourcePrimitiveLeftStepCase
  ; sourcePrimitiveRightStepCase
  ; sourcePureStepCase
  )
open import proof.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)


world-coherent-source-one-step-dispatcher-proofᵀ :
  WorldCoherentSourceOneStepCases →
  WorldCoherentSourceOneStepPrefixᵀ
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (pure-step root) =
  sourcePureStepCase cases prefix coherent exclusive wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ root
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ν-step vV noV) =
  sourceAllocationStepCase cases prefix coherent exclusive wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ vV noV
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-·₁ inner shift) =
  sourceApplicationLeftStepCase cases prefix coherent exclusive wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ inner shift
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-·₂ vV shift inner) =
  sourceApplicationRightStepCase cases prefix coherent exclusive wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ vV shift inner
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-⟨⟩ inner) =
  sourceCastFrameStepCase cases prefix coherent exclusive wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ inner
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-ν inner) =
  sourceNuFrameStepCase cases prefix coherent exclusive wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ inner
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-ν =
  sourceNuBlameStepCase cases prefix coherent exclusive wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-⊕₁ inner shift) =
  sourcePrimitiveLeftStepCase cases prefix coherent exclusive wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ inner shift
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-⊕₂ vL shift inner) =
  sourcePrimitiveRightStepCase cases prefix coherent exclusive wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ vL shift inner
