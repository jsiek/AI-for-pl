module
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationAmbientViewProof
  where

-- File Charter:
--   * Classifies the ambient endpoint relation into the proof-relevant frame
--     view and delegates the unchanged fused closing obligation.
--   * Uses the existing endpoint value, no-bullet, and source-view evidence
--     only to construct the frame view.
--   * Contains no semantic frame case analysis, postulate, or permissive
--     option.

open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameViewᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationAmbientViewDef
  using
    (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationAmbientViewᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingDef
  using
    (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ)


source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-ambient-view-proofᵀ :
  PairedLambdaTargetClosingFrameViewᵀ →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationAmbientViewᵀ
source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-ambient-view-proofᵀ
    frame-view frame-closing prefix coherent exclusive wfL h⇑A reveal
    liftν lift∀
    vV noV vV′ noV′ source-view target-view conversion V⊑V′ =
  frame-closing prefix coherent exclusive wfL h⇑A reveal liftν lift∀
    (frame-view vV noV vV′ noV′ source-view V⊑V′)
    conversion
