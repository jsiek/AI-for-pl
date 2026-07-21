module
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersProof
  where

-- File Charter:
--   * Assembles all thirteen semantic frame-closing handlers from the exact
--     leaf and fused-frame theorem boundaries.
--   * Composes the already checked index and paired-conversion dispatchers so
--     the remaining semantic dependencies are visible in one signature.
--   * Contains no semantic leaf implementation, postulate, hole, permissive
--     option, broad simulation import, or canonical `Lemma` assembly.

open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingHandlers)
open import
  proof.NuImprecisionPairedLambdaTargetClosingGenLeafNuClosingProof
  using (paired-lambda-target-closing-gen-leaf-ν-closing-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingGenLeafNuConversionRotationProof
  using
  (paired-lambda-target-closing-gen-leaf-ν-conversion-rotation-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafClosingProof
  using
  ( paired-lambda-target-closing-lambda-lambda-leaf-closing-proofᵀ
  ; paired-lambda-target-closing-lambda-lambda-leaf-handler-proofᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafPairedConversionCasesDef
  using (PairedLambdaTargetClosingLambdaLambdaLeafPairedConcealClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafPairedConversionCasesProof
  using
  ( paired-lambda-target-closing-lambda-lambda-leaf-paired-conceal-closing-proofᵀ
  ; paired-lambda-target-closing-lambda-lambda-leaf-paired-reveal-closing-proofᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingDef
  using
  (PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingDef
  using
  (PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingLambdaLeafClosingProof
  using (paired-lambda-target-closing-lambda-leaf-handler-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  using (PairedLambdaTargetClosingNuPairedConversionRotationᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedConversionFrameClosingDef
  using (PairedLambdaTargetClosingPairedConversionFrameClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedConversionFrameClosingProof
  using
  (paired-lambda-target-closing-paired-conversion-frame-handler-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameClosingProof
  using
  ( paired-lambda-target-closing-paired-widening-frame-compatible-cases-proofᵀ
  ; paired-lambda-target-closing-paired-widening-frame-handler-proofᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleCasesDef
  using
  (PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreDef
  using
  (PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertProof
  using
  (paired-lambda-target-closing-paired-widening-frame-compatible-source-inert-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceAllFrameAllIndexClosingDef
  using (PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceAllFrameClosingProof
  using
  ( paired-lambda-target-closing-source-all-conceal-frame-closing-proofᵀ
  ; paired-lambda-target-closing-source-all-narrowing-frame-closing-proofᵀ
  ; paired-lambda-target-closing-source-all-reveal-frame-closing-proofᵀ
  ; paired-lambda-target-closing-source-all-widening-frame-closing-proofᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceAllFrameCommutationProof
  using (paired-lambda-target-closing-source-all-frame-commutation-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFrameClosingProof
  using (paired-lambda-target-closing-source-gen-frame-closing-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFrameCommutationProof
  using (paired-lambda-target-closing-source-gen-frame-commutation-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingSourceGenFramePairedConversionCasesProof
  using
  ( paired-lambda-target-closing-source-gen-frame-paired-conceal-closing-proofᵀ
  ; paired-lambda-target-closing-source-gen-frame-paired-reveal-closing-proofᵀ
  )
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
  proof.NuImprecisionPairedLambdaTargetClosingUpGenAllFrameClosingProof
  using (paired-lambda-target-closing-up-gen-all-frame-handler-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpGenLeafAllIndexClosingDef
  using (PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpGenLeafClosingProof
  using
  ( paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ
  ; paired-lambda-target-closing-up-gen-leaf-handler-proofᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpIdFrameClosingProof
  using
  ( paired-lambda-target-closing-up-id-frame-handler-proofᵀ
  ; paired-lambda-target-closing-up-id-frame-widening-cases-proofᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpIdFrameWideningCasesDef
  using
  ( PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ
  ; PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ
  )


paired-lambda-target-closing-frame-closing-handlers-proofᵀ :
  PairedLambdaTargetClosingNuPairedConversionRotationᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ →
  PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ →
  PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ →
  PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingᵀ →
  PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ →
  PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ →
  PairedLambdaTargetClosingPairedConversionFrameClosingᵀ →
  PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ →
  PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ →
  PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ →
  PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ →
  PairedLambdaTargetClosingUpGenAllFrameClosingᵀ →
  PairedLambdaTargetClosingFrameClosingHandlers
paired-lambda-target-closing-frame-closing-handlers-proofᵀ
    rotate lambda-lambda-reveal lambda-lambda-conceal up-gen-all-index
    source-gen-reveal source-gen-conceal source-all-all-index
    paired-conversion paired-widening-source-inert
    paired-widening-target-inert-bridge up-id-id up-id-cast up-gen-all =
  record
    { handle-leaf-ΛΛ =
        paired-lambda-target-closing-lambda-lambda-leaf-handler-proofᵀ
          (paired-lambda-target-closing-lambda-lambda-leaf-closing-proofᵀ
            (paired-lambda-target-closing-lambda-lambda-leaf-paired-reveal-closing-proofᵀ
              lambda-lambda-reveal)
            (paired-lambda-target-closing-lambda-lambda-leaf-paired-conceal-closing-proofᵀ
              lambda-lambda-conceal))
    ; handle-leaf-Λ =
        paired-lambda-target-closing-lambda-leaf-handler-proofᵀ rotate
    ; handle-leaf-gen-ν =
        paired-lambda-target-closing-gen-leaf-ν-closing-proofᵀ
          (paired-lambda-target-closing-gen-leaf-ν-conversion-rotation-proofᵀ
            rotate)
    ; handle-leaf-up-gen =
        paired-lambda-target-closing-up-gen-leaf-handler-proofᵀ
          (paired-lambda-target-closing-up-gen-leaf-closing-proofᵀ
            rotate up-gen-all-index)
    ; handle-frame-gen-all =
        paired-lambda-target-closing-source-gen-frame-closing-proofᵀ
          (paired-lambda-target-closing-source-gen-frame-commutation-proofᵀ
            (paired-lambda-target-closing-source-gen-frame-paired-reveal-closing-proofᵀ
              source-gen-reveal)
            (paired-lambda-target-closing-source-gen-frame-paired-conceal-closing-proofᵀ
              source-gen-conceal))
    ; handle-frame-cast⊒⊑ =
        paired-lambda-target-closing-source-all-narrowing-frame-closing-proofᵀ
          source-all-commutation
    ; handle-frame-cast⊑⊑ =
        paired-lambda-target-closing-source-all-widening-frame-closing-proofᵀ
          source-all-commutation
    ; handle-frame-conv↑⊑ =
        paired-lambda-target-closing-source-all-reveal-frame-closing-proofᵀ
          source-all-commutation
    ; handle-frame-conv↓⊑ =
        paired-lambda-target-closing-source-all-conceal-frame-closing-proofᵀ
          source-all-commutation
    ; handle-frame-paired-conversion =
        paired-lambda-target-closing-paired-conversion-frame-handler-proofᵀ
          paired-conversion
    ; handle-frame-paired-widening =
        paired-lambda-target-closing-paired-widening-frame-handler-proofᵀ
          (paired-lambda-target-closing-paired-widening-frame-compatible-cases-proofᵀ
            (paired-lambda-target-closing-paired-widening-frame-compatible-source-inert-proofᵀ
              paired-widening-source-inert)
            paired-widening-target-inert-bridge)
    ; handle-frame-up-id =
        paired-lambda-target-closing-up-id-frame-handler-proofᵀ
          (paired-lambda-target-closing-up-id-frame-widening-cases-proofᵀ
            up-id-id up-id-cast)
    ; handle-frame-up-gen-all =
        paired-lambda-target-closing-up-gen-all-frame-handler-proofᵀ
          up-gen-all
    }
  where
  source-all-commutation =
    paired-lambda-target-closing-source-all-frame-commutation-proofᵀ
      rotate source-all-all-index
