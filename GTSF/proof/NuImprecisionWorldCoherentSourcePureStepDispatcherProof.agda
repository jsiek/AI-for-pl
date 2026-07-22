module
  proof.NuImprecisionWorldCoherentSourcePureStepDispatcherProof
  where

-- File Charter:
--   * Assembles the exact source pure-step theorem from four source-shape
--     capabilities.
--   * Dispatches exhaustively over every root constructor in `NuReduction`.
--   * Contains no semantic case implementation, catch-all, postulate, hole,
--     or permissive option.

open import NuReduction using
  ( blame-·₁
  ; blame-·₂
  ; blame-•
  ; blame-⟨⟩
  ; blame-⊕₁
  ; blame-⊕₂
  ; seal-unseal
  ; tag-untag-bad
  ; tag-untag-ok
  ; β
  ; β-gen•
  ; β-id
  ; β-inst
  ; β-seq
  ; β-Λ•
  ; β-∀•
  ; β-↦
  ; δ-⊕
  )
open import proof.NuImprecisionWorldCoherentSourcePureStepCasesDef using
  ( WorldCoherentSourcePureStepCases
  ; WorldCoherentSourcePureStepᵀ
  ; sourceApplicationPureRootCase
  ; sourceCastPureRootCase
  ; sourcePrimitivePureRootCase
  ; sourceRuntimeBulletPureRootCase
  )


world-coherent-source-pure-step-dispatcher-proofᵀ :
  WorldCoherentSourcePureStepCases →
  WorldCoherentSourcePureStepᵀ
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ δ-⊕ =
  sourcePrimitivePureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ δ-⊕
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β vV) =
  sourceApplicationPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β vV)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-Λ• vV) =
  sourceRuntimeBulletPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-Λ• vV)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-∀• vV) =
  sourceRuntimeBulletPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-∀• vV)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-gen• vV) =
  sourceRuntimeBulletPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-gen• vV)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-id vV) =
  sourceCastPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-id vV)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-seq vV) =
  sourceCastPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-seq vV)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-↦ vV vW) =
  sourceApplicationPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-↦ vV vW)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-inst vV) =
  sourceCastPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-inst vV)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (tag-untag-ok vV) =
  sourceCastPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (tag-untag-ok vV)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (tag-untag-bad vV G≢H) =
  sourceCastPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (tag-untag-bad vV G≢H)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (seal-unseal vV) =
  sourceCastPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (seal-unseal vV)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-·₁ =
  sourceApplicationPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-·₁
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (blame-·₂ vV) =
  sourceApplicationPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (blame-·₂ vV)
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-• =
  sourceRuntimeBulletPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-•
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-⟨⟩ =
  sourceCastPureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-⟨⟩
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-⊕₁ =
  sourcePrimitivePureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-⊕₁
world-coherent-source-pure-step-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (blame-⊕₂ vL) =
  sourcePrimitivePureRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (blame-⊕₂ vL)
