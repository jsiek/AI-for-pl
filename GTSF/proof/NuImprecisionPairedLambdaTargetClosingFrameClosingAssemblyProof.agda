module
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingAssemblyProof
  where

-- File Charter:
--   * Connects the complete semantic-handler assembly and shared target-frame
--     capability to the final proof-relevant frame-closing theorem.
--   * Exposes every remaining semantic dependency in the final consumer's
--     checked type, providing the top-level fit skeleton below DGG catch-up.
--   * Contains no semantic implementation, postulate, hole, permissive
--     option, broad simulation import, or canonical `Lemma` assembly.

open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersProof
  using (paired-lambda-target-closing-frame-closing-handlers-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingProof
  using (paired-lambda-target-closing-frame-closing-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameDef
  using (PairedLambdaTargetClosingFrameClosingTargetFrameᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafPairedConversionCasesDef
  using
  ( PairedLambdaTargetClosingLambdaLambdaLeafPairedConcealClosingᵀ
  ; PairedLambdaTargetClosingLambdaLambdaLeafPairedRevealClosingᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  using (PairedLambdaTargetClosingNuPairedConversionRotationᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedConversionFrameClosingDef
  using (PairedLambdaTargetClosingPairedConversionFrameClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameClosingDef
  using (PairedLambdaTargetClosingPairedWideningFrameClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceAllFrameAllIndexClosingDef
  using (PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFramePairedConversionCasesDef
  using
  ( PairedLambdaTargetClosingSourceGenFramePairedConcealClosingᵀ
  ; PairedLambdaTargetClosingSourceGenFramePairedRevealClosingᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpGenAllFrameClosingDef
  using (PairedLambdaTargetClosingUpGenAllFrameClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpGenLeafAllIndexClosingDef
  using (PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpIdFrameClosingDef
  using (PairedLambdaTargetClosingUpIdFrameClosingᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingDef
  using
  (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ)


paired-lambda-target-closing-frame-closing-assembly-proofᵀ :
  PairedLambdaTargetClosingNuPairedConversionRotationᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafPairedRevealClosingᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafPairedConcealClosingᵀ →
  PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ →
  PairedLambdaTargetClosingSourceGenFramePairedRevealClosingᵀ →
  PairedLambdaTargetClosingSourceGenFramePairedConcealClosingᵀ →
  PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ →
  PairedLambdaTargetClosingPairedConversionFrameClosingᵀ →
  PairedLambdaTargetClosingPairedWideningFrameClosingᵀ →
  PairedLambdaTargetClosingUpIdFrameClosingᵀ →
  PairedLambdaTargetClosingUpGenAllFrameClosingᵀ →
  PairedLambdaTargetClosingFrameClosingTargetFrameᵀ →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ
paired-lambda-target-closing-frame-closing-assembly-proofᵀ
    rotate lambda-lambda-reveal lambda-lambda-conceal up-gen-all-index
    source-gen-reveal source-gen-conceal source-all-all-index
    paired-conversion paired-widening up-id up-gen-all target-frame =
  paired-lambda-target-closing-frame-closing-proofᵀ
    (paired-lambda-target-closing-frame-closing-handlers-proofᵀ
      rotate lambda-lambda-reveal lambda-lambda-conceal up-gen-all-index
      source-gen-reveal source-gen-conceal source-all-all-index
      paired-conversion paired-widening up-id up-gen-all)
    target-frame
