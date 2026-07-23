module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingCapabilitiesDef
  where

-- File Charter:
--   * Bundles the exact semantic capabilities required by the paired-lambda
--     target-closing frame-closing assembly.
--   * Gives upper assemblies one explicit dependency boundary while retaining
--     the independently checkable statements of all twenty-one capabilities.
--   * Contains no proofs, postulates, holes, permissive options, or imports of
--     proof implementations.

open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameCasesDef
  using
  ( PairedLambdaTargetClosingFrameClosingTargetConcealᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetIdOnlyWideningᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetNarrowingᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetWideningᵀ
  )
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetRevealCoreDef
  using (PairedLambdaTargetClosingFrameClosingTargetRevealCoreᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingDef
  using
  (PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ)
open import
  proof.PairedLambda.LambdaLeaves.Structural.NuImprecisionPairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingDef
  using
  (PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedConversionFramePairedConversionCasesDef
  using
  ( PairedLambdaTargetClosingPairedConversionFramePairedConcealClosingᵀ
  ; PairedLambdaTargetClosingPairedConversionFramePairedRevealClosingᵀ
  )
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleCasesDef
  using
  (PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ)
open import
  proof.PairedLambda.Conversions.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreDef
  using
  (PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceAll.NuImprecisionPairedLambdaTargetClosingSourceAllFrameAllIndexClosingDef
  using (PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingDef
  using (PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.SourceGen.NuImprecisionPairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreDef
  using
  (PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreᵀ)
open import
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpGenAllFrameWideningCasesDef
  using
  ( PairedLambdaTargetClosingUpGenAllFrameQuotientCastWideningClosingᵀ
  ; PairedLambdaTargetClosingUpGenAllFrameQuotientIdWideningClosingᵀ
  )
open import
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpGenLeafAllIndexClosingDef
  using (PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ)
open import
  proof.PairedLambda.SourceFrames.UpFrames.NuImprecisionPairedLambdaTargetClosingUpIdFrameWideningCasesDef
  using
  ( PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ
  ; PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ
  )
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetStructuralHalfSquareDef
  using
  ( PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ
  ; PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ
  )


record PairedLambdaTargetClosingFrameClosingCapabilities : Set₁ where
  field
    cap-fresh-path-target-structural-reveal-half-square :
      PairedUniversalConversionFreshPathTargetStructuralRevealHalfSquareᵀ
    cap-fresh-path-target-structural-conceal-half-square :
      PairedUniversalConversionFreshPathTargetStructuralConcealHalfSquareᵀ
    cap-lambda-lambda-structural-reveal :
      PairedLambdaTargetClosingLambdaLambdaLeafStructuralRevealClosingᵀ
    cap-lambda-lambda-structural-conceal :
      PairedLambdaTargetClosingLambdaLambdaLeafStructuralConcealClosingᵀ
    cap-up-gen-leaf-all-index :
      PairedLambdaTargetClosingUpGenLeafAllIndexClosingᵀ
    cap-source-gen-structural-reveal-core :
      PairedLambdaTargetClosingSourceGenFrameStructuralRevealClosingCoreᵀ
    cap-source-gen-structural-conceal :
      PairedLambdaTargetClosingSourceGenFrameStructuralConcealClosingᵀ
    cap-source-all-all-index :
      PairedLambdaTargetClosingSourceAllFrameAllIndexClosingᵀ
    cap-paired-conversion-reveal :
      PairedLambdaTargetClosingPairedConversionFramePairedRevealClosingᵀ
    cap-paired-conversion-conceal :
      PairedLambdaTargetClosingPairedConversionFramePairedConcealClosingᵀ
    cap-paired-widening-source-inert-core :
      PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ
    cap-paired-widening-target-inert-bridge :
      PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ
    cap-up-id-quotient-id-widening :
      PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ
    cap-up-id-quotient-cast-widening :
      PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ
    cap-up-gen-all-quotient-id-widening :
      PairedLambdaTargetClosingUpGenAllFrameQuotientIdWideningClosingᵀ
    cap-up-gen-all-quotient-cast-widening :
      PairedLambdaTargetClosingUpGenAllFrameQuotientCastWideningClosingᵀ
    cap-target-reveal-core :
      PairedLambdaTargetClosingFrameClosingTargetRevealCoreᵀ
    cap-target-conceal :
      PairedLambdaTargetClosingFrameClosingTargetConcealᵀ
    cap-target-narrowing :
      PairedLambdaTargetClosingFrameClosingTargetNarrowingᵀ
    cap-target-widening :
      PairedLambdaTargetClosingFrameClosingTargetWideningᵀ
    cap-target-id-only-widening :
      PairedLambdaTargetClosingFrameClosingTargetIdOnlyWideningᵀ
