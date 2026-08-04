module
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootProof
  where

-- File Charter:
--   * Proves the complete source application pure-root outcome boundary from
--     the two beta capabilities.
--   * Wraps related lambda and blame-root results while passing the
--     function-cast beta outcome through unchanged.
--   * Discharges both application-blame reductions with the canonical shared
--     source keep-step blame proof.
--   * Contains no semantic beta implementation, result/view carrier,
--     postulate, hole, catch-all, or permissive option.

open import NuReduction using
  (blame-·₁; blame-·₂; pure-step; β; β-↦)
open import
  proof.Source.OneStep.NuImprecisionSourceOneStepBlameRootProof using
  (world-coherent-source-keep-blame-root-proofᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef
  using (source-step-outcome-related)
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using
  ( WorldCoherentSourceApplicationPureRootCases
  ; sourceFunctionCastBetaRootCase
  ; sourceLambdaBetaRootCase
  )
open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootDef
  using (WorldCoherentSourceApplicationPureRootᵀ)


world-coherent-source-application-pure-root-proofᵀ :
  WorldCoherentSourceApplicationPureRootCases →
  WorldCoherentSourceApplicationPureRootᵀ
world-coherent-source-application-pure-root-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β vV) =
  source-step-outcome-related
    (sourceLambdaBetaRootCase cases
      prefix coherent exclusive unique wfL wfR okM okM′
      M⊢ M′⊢ M⊑M′ vV)
world-coherent-source-application-pure-root-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-↦ vV vW) =
  sourceFunctionCastBetaRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ vV vW
world-coherent-source-application-pure-root-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-·₁ =
  source-step-outcome-related
    (world-coherent-source-keep-blame-root-proofᵀ
      prefix coherent exclusive unique wfL wfR okM okM′
      M⊢ M′⊢ M⊑M′ (pure-step blame-·₁))
world-coherent-source-application-pure-root-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (blame-·₂ vV) =
  source-step-outcome-related
    (world-coherent-source-keep-blame-root-proofᵀ
      prefix coherent exclusive unique wfL wfR okM okM′
      M⊢ M′⊢ M⊑M′ (pure-step (blame-·₂ vV)))
