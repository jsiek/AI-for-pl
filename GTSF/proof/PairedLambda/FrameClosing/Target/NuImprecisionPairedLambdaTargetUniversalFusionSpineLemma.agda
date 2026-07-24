module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetUniversalFusionSpineLemma
  where

-- File Charter:
--   * Exposes the canonical fold from framed recursive target universal
--     fusion spines to quotiented term imprecision.
--   * Supplies the completed pure-spine and paired-lambda-frame folds.
--   * Contains no extraction, simulation result, Resume dependency, postulate,
--     hole, permissive option, or termination bypass.

open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewProperties
  using (paired-lambda-target-closing-frame-view-frames-relation)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetUniversalFusionSpineDef
  using (PairedLambdaTargetUniversalFusionSpineRelationᵀ)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetUniversalFusionSpineProof
  using
  (paired-lambda-target-universal-fusion-spine-relation-proofᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetUniversalFusionSpineLemma
  using (target-universal-fusion-spine-relationᵀ)


paired-lambda-target-universal-fusion-spine-relationᵀ :
  PairedLambdaTargetUniversalFusionSpineRelationᵀ
paired-lambda-target-universal-fusion-spine-relationᵀ =
  paired-lambda-target-universal-fusion-spine-relation-proofᵀ
    target-universal-fusion-spine-relationᵀ
    paired-lambda-target-closing-frame-view-frames-relation
