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
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameCasesDef
  using
  ( PairedLambdaTargetClosingFrameClosingTargetConcealᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetIdOnlyWideningᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetNarrowingᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetRevealᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetWideningᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameProof
  using (paired-lambda-target-closing-frame-closing-target-frame-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingDef
  using
  (PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingDef
  using
  (PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  using (PairedLambdaTargetClosingNuPairedConversionRotationᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedConversionFrameClosingDef
  using (PairedLambdaTargetClosingPairedConversionFrameClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleCasesDef
  using
  ( PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertᵀ
  ; PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceAllFrameAllIndexClosingDef
  using (PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingDef
  using (PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingDef
  using (PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpGenAllFrameClosingDef
  using (PairedLambdaTargetClosingUpGenAllFrameClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpGenLeafAllIndexClosingDef
  using (PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpIdFrameWideningCasesDef
  using
  ( PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ
  ; PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ
  )
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingDef
  using
  (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ)


paired-lambda-target-closing-frame-closing-assembly-proofᵀ :
  PairedLambdaTargetClosingNuPairedConversionRotationᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ →
  PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ →
  PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ →
  PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ →
  PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ →
  PairedLambdaTargetClosingPairedConversionFrameClosingᵀ →
  PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertᵀ →
  PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ →
  PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ →
  PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ →
  PairedLambdaTargetClosingUpGenAllFrameClosingᵀ →
  PairedLambdaTargetClosingFrameClosingTargetRevealᵀ →
  PairedLambdaTargetClosingFrameClosingTargetConcealᵀ →
  PairedLambdaTargetClosingFrameClosingTargetNarrowingᵀ →
  PairedLambdaTargetClosingFrameClosingTargetWideningᵀ →
  PairedLambdaTargetClosingFrameClosingTargetIdOnlyWideningᵀ →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ
paired-lambda-target-closing-frame-closing-assembly-proofᵀ
    rotate lambda-lambda-reveal lambda-lambda-conceal up-gen-all-index
    source-gen-reveal source-gen-conceal source-all-all-index
    paired-conversion paired-widening-source-inert
    paired-widening-target-inert-bridge up-id-id up-id-cast up-gen-all
    target-reveal target-conceal target-narrowing target-widening
    target-id-only-widening =
  paired-lambda-target-closing-frame-closing-proofᵀ
    (paired-lambda-target-closing-frame-closing-handlers-proofᵀ
      rotate lambda-lambda-reveal lambda-lambda-conceal up-gen-all-index
      source-gen-reveal source-gen-conceal source-all-all-index
      paired-conversion paired-widening-source-inert
      paired-widening-target-inert-bridge up-id-id up-id-cast up-gen-all)
    (paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
      target-reveal target-conceal target-narrowing target-widening
      target-id-only-widening)
