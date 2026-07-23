module
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupAssemblyProof
  where

-- File Charter:
--   * Connects common continuation-value terminal closing to the whole
--     post-beta target-closing catch-up theorem.
--   * Adds only the independently stated terminal value-catch-up and active
--     fresh-unseal capabilities above structural-all relation assembly.
--   * Contains no semantic leaf implementation, postulate, hole, permissive
--     option, broad simulation import, or canonical `Lemma` assembly.

open import
  proof.PairedLambda.Continuation.ValueTerminal.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalDef
  using (PairedLambdaTargetClosingContinuationValueTerminalᵀ)
open import
  proof.Source.NuPaired.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationAssemblyProof
  using
  (source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-assembly-proofᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupDef
  using
  (WorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupProof
  using
  (world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-proofᵀ)
open import
  proof.WorldCoherent.Source.NuPaired.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupDef
  using
  (WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-assembly-proofᵀ :
  PairedLambdaTargetClosingContinuationValueTerminalᵀ →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ →
  WorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupᵀ
world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-assembly-proofᵀ
    terminal value-catchup unseal-catchup =
  world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-proofᵀ
    (source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-assembly-proofᵀ
      terminal)
    value-catchup unseal-catchup
