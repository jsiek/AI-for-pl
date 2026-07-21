module
  proof.NuImprecisionPairedLambdaTargetClosingPairedConversionFrameClosingProof
  where

-- File Charter:
--   * Proves the reusable fused paired-conversion frame theorem from its exact
--     paired-reveal and paired-conceal constructor branches.
--   * Adapts that fused theorem to the exact target-closing handler field.
--   * Keeps the semantic theorem as an explicit higher-order dependency and
--     preserves both the recursive motive and exact inner frame view.
--   * Contains no semantic branch implementation, postulate, hole, permissive
--     option, one-sided intermediate, broad simulation import, or recursive
--     frame-closing dependency.

import Coercions as C
open import Coercions using (Coercion; Inert)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedConversion
  ; paired-conceal
  ; paired-reveal
  )
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedConversionFrameClosingDef
  using (PairedLambdaTargetClosingPairedConversionFrameClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedConversionFramePairedConversionCasesDef
  using
  ( PairedLambdaTargetClosingPairedConversionFramePairedConcealClosingᵀ
  ; PairedLambdaTargetClosingPairedConversionFramePairedRevealClosingᵀ
  )


paired-lambda-target-closing-paired-conversion-frame-closing-proofᵀ :
  PairedLambdaTargetClosingPairedConversionFramePairedRevealClosingᵀ →
  PairedLambdaTargetClosingPairedConversionFramePairedConcealClosingᵀ →
  PairedLambdaTargetClosingPairedConversionFrameClosingᵀ
paired-lambda-target-closing-paired-conversion-frame-closing-proofᵀ
    reveal-closing conceal-closing inner view inert
    (paired-reveal corr source-reveal target-reveal)
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    final-conversion =
  reveal-closing inner view inert corr source-reveal target-reveal
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    final-conversion
paired-lambda-target-closing-paired-conversion-frame-closing-proofᵀ
    reveal-closing conceal-closing inner view inert
    (paired-conceal corr source-conceal target-conceal)
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    final-conversion =
  conceal-closing inner view inert corr source-conceal target-conceal
    prefix coherent exclusive wfL h⇑A final-reveal liftν lift∀
    final-conversion


paired-lambda-target-closing-paired-conversion-frame-handler-proofᵀ :
  PairedLambdaTargetClosingPairedConversionFrameClosingᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ C′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
    {c c′ : Coercion} →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ
    W W′ (`∀ B) B′ q →
  Inert c′ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′ q r →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (W ⟨ C.`∀ c ⟩) (W′ ⟨ c′ ⟩) C C′ r
paired-lambda-target-closing-paired-conversion-frame-handler-proofᵀ
    closing inner view inert conversion =
  closing inner view inert conversion
