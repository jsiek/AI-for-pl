module
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameProof
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
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameCasesDef
  using
  ( PairedLambdaTargetClosingFrameClosingTargetConcealᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetIdOnlyWideningᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetNarrowingᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetRevealᵀ
  ; PairedLambdaTargetClosingFrameClosingTargetWideningᵀ
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameDef
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
    (inj₁ (_ , _ , _ , reveal)) =
  target-reveal inner view inert reveal
paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
    target-reveal target-conceal target-narrowing target-widening
    target-id-only-widening inner view inert
    (inj₂ (inj₁ (_ , _ , _ , conceal))) =
  target-conceal inner view inert conceal
paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
    target-reveal target-conceal target-narrowing target-widening
    target-id-only-widening inner view inert
    (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , narrowing)))) =
  target-narrowing inner view inert mode seal★ narrowing
paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
    target-reveal target-conceal target-narrowing target-widening
    target-id-only-widening inner view inert
    (inj₂ (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , widening))))) =
  target-widening inner view inert mode seal★ widening
paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
    target-reveal target-conceal target-narrowing target-widening
    target-id-only-widening inner view inert
    (inj₂ (inj₂ (inj₂ (inj₂ (seal★ , widening))))) =
  target-id-only-widening inner view inert seal★ widening
