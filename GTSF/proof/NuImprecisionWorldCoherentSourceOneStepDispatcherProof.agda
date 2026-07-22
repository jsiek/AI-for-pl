module proof.NuImprecisionWorldCoherentSourceOneStepDispatcherProof where

-- File Charter:
--   * Proves that the nine frozen source-reduction case capabilities assemble
--     into the ambient-prefix source one-step outcome dispatcher.
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
  ; sourcePureStepCases
  )
open import proof.NuImprecisionWorldCoherentSourceOneStepOutcomeDef using
  (source-step-outcome-related)
open import proof.NuImprecisionWorldCoherentSourcePureStepDispatcherProof using
  (world-coherent-source-pure-step-dispatcher-proofᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)


world-coherent-source-one-step-dispatcher-proofᵀ :
  WorldCoherentSourceOneStepCases →
  WorldCoherentSourceOneStepPrefixᵀ
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (pure-step root) =
  source-step-outcome-related
    (world-coherent-source-pure-step-dispatcher-proofᵀ
      (sourcePureStepCases cases)
      prefix coherent exclusive unique wfL wfR okM okM′
      M⊢ M′⊢ M⊑M′ root)
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ν-step vV noV) =
  source-step-outcome-related
    (sourceAllocationStepCase cases prefix coherent exclusive unique wfL wfR
      okM okM′ M⊢ M′⊢ M⊑M′ vV noV)
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-·₁ inner shift) =
  sourceApplicationLeftStepCase cases prefix coherent exclusive unique wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ inner shift
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-·₂ vV shift inner) =
  sourceApplicationRightStepCase cases prefix coherent exclusive unique wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ vV shift inner
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-⟨⟩ inner) =
  sourceCastFrameStepCase cases prefix coherent exclusive unique wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ inner
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-ν inner) =
  sourceNuFrameStepCase cases prefix coherent exclusive unique wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ inner
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-ν =
  source-step-outcome-related
    (sourceNuBlameStepCase cases prefix coherent exclusive unique wfL wfR
      okM okM′ M⊢ M′⊢ M⊑M′)
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-⊕₁ inner shift) =
  sourcePrimitiveLeftStepCase cases prefix coherent exclusive unique wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ inner shift
world-coherent-source-one-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (ξ-⊕₂ vL shift inner) =
  sourcePrimitiveRightStepCase cases prefix coherent exclusive unique wfL wfR
    okM okM′ M⊢ M′⊢ M⊑M′ vL shift inner
