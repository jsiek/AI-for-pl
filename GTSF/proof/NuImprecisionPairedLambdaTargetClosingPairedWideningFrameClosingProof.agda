module
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameClosingProof
  where

-- File Charter:
--   * Adapts the reusable fused paired-widening frame theorem to the exact
--     target-closing handler field.
--   * Keeps the semantic theorem as an explicit higher-order dependency and
--     preserves the recursive motive, frame view, both cast/seal modes, both
--     widening typings, and compatibility evidence.
--   * Contains no postulate, hole, permissive option, one-sided intermediate,
--     broad simulation import, or recursive frame-closing dependency.

import Coercions as C
open import Coercions using (Coercion; Inert; ModeEnv)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import PairedWideningCompatibility using
  ( PairedWideningCompatible
  ; compatible-source-inert
  ; compatible-target-inert-bridge
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameClosingDef
  using (PairedLambdaTargetClosingPairedWideningFrameClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleCasesDef
  using
  ( PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertᵀ
  ; PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ
  )


paired-lambda-target-closing-paired-widening-frame-compatible-cases-proofᵀ :
  PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertᵀ →
  PairedLambdaTargetClosingPairedWideningFrameCompatibleTargetInertBridgeᵀ →
  PairedLambdaTargetClosingPairedWideningFrameClosingᵀ
paired-lambda-target-closing-paired-widening-frame-compatible-cases-proofᵀ
    source-inert target-inert-bridge inner view inert-d′
    cast-mode seal source-widening target-cast-mode target-seal
    target-widening (compatible-source-inert inert-d) =
  source-inert inner view inert-d′ cast-mode seal source-widening
    target-cast-mode target-seal target-widening inert-d
paired-lambda-target-closing-paired-widening-frame-compatible-cases-proofᵀ
    source-inert target-inert-bridge inner view inert-d′
    cast-mode seal source-widening target-cast-mode target-seal
    target-widening (compatible-target-inert-bridge bridge) =
  target-inert-bridge inner view inert-d′ cast-mode seal source-widening
    target-cast-mode target-seal target-widening bridge


paired-lambda-target-closing-paired-widening-frame-handler-proofᵀ :
  PairedLambdaTargetClosingPairedWideningFrameClosingᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ C′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
    {c c′ : Coercion} {μ μ′ : ModeEnv} →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ
    W W′ (`∀ B) B′ q →
  Inert c′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ C.`∀ c ∶ `∀ B ⊑ `∀ C →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ B′ ⊑ C′ →
  PairedWideningCompatible Φ Δᴸ Δᴿ
    (C.`∀ c) c′ (`∀ C) B′ →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    (W ⟨ C.`∀ c ⟩) (W′ ⟨ c′ ⟩) C C′ r
paired-lambda-target-closing-paired-widening-frame-handler-proofᵀ
    closing inner view inert cast-mode seal source-widening
    target-cast-mode target-seal target-widening compat =
  closing inner view inert cast-mode seal source-widening
    target-cast-mode target-seal target-widening compat
