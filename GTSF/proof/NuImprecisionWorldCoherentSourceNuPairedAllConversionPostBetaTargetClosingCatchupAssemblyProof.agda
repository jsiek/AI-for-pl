module
  proof.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupAssemblyProof
  where

-- File Charter:
--   * Connects the continuation-indexed target-closing handlers to the whole
--     post-beta target-closing catch-up theorem.
--   * Adds only the independently stated terminal value-catch-up and active
--     fresh-unseal capabilities above structural-all relation assembly.
--   * Contains no semantic leaf implementation, postulate, hole, permissive
--     option, broad simulation import, or canonical `Lemma` assembly.

open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationHandlersDef
  using (PairedLambdaTargetClosingContinuationHandlers)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationAssemblyProof
  using
  (source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-assembly-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupDef
  using
  (WorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupProof
  using
  (world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupDef
  using
  (WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-assembly-proofᵀ :
  PairedLambdaTargetClosingContinuationHandlers →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentSourceNuPairedAllConversionPostBetaUnsealClosingCatchupᵀ →
  WorldCoherentSourceNuPairedAllConversionPostBetaTargetClosingCatchupᵀ
world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-assembly-proofᵀ
    handlers value-catchup unseal-catchup =
  world-coherent-source-ν-paired-all-conversion-post-beta-target-closing-catchup-proofᵀ
    (source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-assembly-proofᵀ
      handlers)
    value-catchup unseal-catchup
