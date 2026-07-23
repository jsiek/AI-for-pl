module
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootProof
  where

-- File Charter:
--   * Proves the complete source application pure-root boundary from the two
--     exact beta capabilities.
--   * Discharges both application-blame reductions with the canonical shared
--     source keep-step blame proof.
--   * Contains no semantic beta implementation, result/view carrier,
--     postulate, hole, catch-all, or permissive option.

open import NuReduction using
  (blame-·₁; blame-·₂; pure-step; β; β-↦)
open import
  proof.NuImprecisionSourceOneStepBlameRootProof using
  (world-coherent-source-keep-blame-root-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using
  ( WorldCoherentSourceApplicationPureRootCases
  ; sourceFunctionCastBetaRootCase
  ; sourceLambdaBetaRootCase
  )
open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootDef
  using (WorldCoherentSourceApplicationPureRootᵀ)


world-coherent-source-application-pure-root-proofᵀ :
  WorldCoherentSourceApplicationPureRootCases →
  WorldCoherentSourceApplicationPureRootᵀ
world-coherent-source-application-pure-root-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β vV) =
  sourceLambdaBetaRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ vV
world-coherent-source-application-pure-root-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (β-↦ vV vW) =
  sourceFunctionCastBetaRootCase cases
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ vV vW
world-coherent-source-application-pure-root-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-·₁ =
  world-coherent-source-keep-blame-root-proofᵀ
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (pure-step blame-·₁)
world-coherent-source-application-pure-root-proofᵀ
    cases prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (blame-·₂ vV) =
  world-coherent-source-keep-blame-root-proofᵀ
    prefix coherent exclusive unique wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (pure-step (blame-·₂ vV))
