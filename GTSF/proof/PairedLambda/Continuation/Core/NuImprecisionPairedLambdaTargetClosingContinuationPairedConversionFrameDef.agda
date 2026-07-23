module
  proof.PairedLambda.Continuation.Core.NuImprecisionPairedLambdaTargetClosingContinuationPairedConversionFrameDef
  where

-- File Charter:
--   * Defines the complete continuation-indexed paired-conversion frame
--     contract as a standalone theorem statement.
--   * Retains the recursive continuation motive and exact proof-relevant
--     inner frame view from the continuation-handler boundary.
--   * Contains no handler projection, implementation, postulate, hole,
--     permissive option, or broad simulation import.

import Coercions as C
open import Coercions using (Coercion; Inert)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using (PairedConversion)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationPairedConversionFrameᵀ : Set₁
PairedLambdaTargetClosingContinuationPairedConversionFrameᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ C′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
    {c c′ : Coercion} →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ
    W W′ (`∀ B) B′ q →
  Inert c′ →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′ q r →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    (W ⟨ C.`∀ c ⟩) (W′ ⟨ c′ ⟩) C C′ r
