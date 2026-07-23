module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameProof
  where

-- File Charter:
--   * Dispatches the shared target-only frame capability to five exact
--     semantic branch contracts.
--   * Eliminates the existing nested reveal/conceal/narrowing/widening/id-only
--     sum by exhaustive explicit cases.
--   * Performs no recursive frame closing and changes no shared target-frame
--     definition or public API.
--   * Contains no handler import, postulate, hole, permissive option,
--     incomplete match, recursive frame-closing dependency, or broad
--     simulation import.

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameCasesDef
  using
  ( PairedLambdaTargetClosingFrameClosingTargetConcealᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetIdOnlyWideningᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetNarrowingᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetRevealᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetWideningᵀ
  )
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameDef
  using (PairedLambdaTargetClosingFrameClosingTargetFrameᵀ)


paired-lambda-target-closing-frame-closing-target-frame-proofᵀ :
  PairedLambdaTargetClosingFrameClosingTargetRevealᵀ →
  PairedLambdaTargetClosingFrameClosingTargetConcealᵀ →
  PairedLambdaTargetClosingFrameClosingTargetNarrowingᵀ →
  PairedLambdaTargetClosingFrameClosingTargetWideningᵀ →
  PairedLambdaTargetClosingFrameClosingTargetIdOnlyWideningᵀ →
  PairedLambdaTargetClosingFrameClosingTargetFrameᵀ
paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
    target-reveal target-conceal target-narrowing target-widening
    target-id-only-widening inner view inert
    (inj₁ (_ , _ , _ , reveal))
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion =
  target-reveal inner view inert reveal
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion
paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
    target-reveal target-conceal target-narrowing target-widening
    target-id-only-widening inner view inert
    (inj₂ (inj₁ (_ , _ , _ , conceal)))
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion =
  target-conceal inner view inert conceal
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion
paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
    target-reveal target-conceal target-narrowing target-widening
    target-id-only-widening inner view inert
    (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , narrowing))))
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion =
  target-narrowing inner view inert mode seal★ narrowing
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion
paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
    target-reveal target-conceal target-narrowing target-widening
    target-id-only-widening inner view inert
    (inj₂ (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , widening)))))
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion =
  target-widening inner view inert mode seal★ widening
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion
paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
    target-reveal target-conceal target-narrowing target-widening
    target-id-only-widening inner view inert
    (inj₂ (inj₂ (inj₂ (inj₂ (seal★ , widening)))))
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion =
  target-id-only-widening inner view inert seal★ widening
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    conversion
