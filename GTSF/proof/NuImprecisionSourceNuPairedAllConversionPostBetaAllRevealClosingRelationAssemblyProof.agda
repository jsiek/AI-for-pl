module
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationAssemblyProof
  where

-- File Charter:
--   * Connects the continuation-indexed semantic handlers through frame
--     closing, ambient-prefix adaptation, and universal canonical-form
--     inversion to the structural-all closing relation used by catch-up.
--   * Provides a strict fit check one consumer above the frame interpreter.
--   * Contains no semantic leaf implementation, postulate, hole, permissive
--     option, broad simulation import, or canonical `Lemma` assembly.

open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationHandlersDef
  using (PairedLambdaTargetClosingContinuationHandlers)
open import
  proof.NuImprecisionPairedLambdaTargetClosingContinuationProof
  using (paired-lambda-target-closing-continuation-proofᵀ)
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
  PairedLambdaTargetClosingContinuationHandlers →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ
source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-assembly-proofᵀ
    handlers =
  source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-proofᵀ
    (source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-ambient-view-proofᵀ
      paired-lambda-target-closing-frame-view-proofᵀ
      (paired-lambda-target-closing-continuation-proofᵀ
        handlers))
