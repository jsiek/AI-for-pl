module
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationAssemblyProof
  where

-- File Charter:
--   * Connects common continuation-value terminal closing through direct
--     frame-view projection, ambient-prefix adaptation, and universal
--     canonical-form inversion to the structural-all closing relation.
--   * Provides a strict fit check without the thirteen-handler interpreter.
--   * Contains no semantic leaf implementation, postulate, hole, permissive
--     option, broad simulation import, or canonical `Lemma` assembly.

open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationFromViewProof
  using
  ( paired-lambda-target-closing-continuation-from-view-frame-closing-proofᵀ
  ; paired-lambda-target-closing-continuation-from-view-proofᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalDef
  using (PairedLambdaTargetClosingContinuationValueTerminalᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewProof
  using (paired-lambda-target-closing-frame-view-proofᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationAmbientViewProof
  using
  (source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-ambient-view-proofᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationDef
  using (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationProof
  using
  (source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-proofᵀ)


source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-assembly-proofᵀ :
  PairedLambdaTargetClosingContinuationValueTerminalᵀ →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ
source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-assembly-proofᵀ
    terminal =
  source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-proofᵀ
    (source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-ambient-view-proofᵀ
      paired-lambda-target-closing-frame-view-proofᵀ
      (paired-lambda-target-closing-continuation-from-view-frame-closing-proofᵀ
        (paired-lambda-target-closing-continuation-from-view-proofᵀ
          terminal)))
