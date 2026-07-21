module
  proof.NuImprecisionPairedLambdaTargetClosingUpIdFrameClosingProof
  where

-- File Charter:
--   * Adapts the reusable fused quotient up-id frame theorem to the exact
--     target-closing handler field.
--   * Provides the exhaustive constructor dispatcher from the quotient-id and
--     quotient-cast branch capabilities to the whole quotient widening pair.
--   * Keeps the semantic theorem as an explicit higher-order dependency and
--     preserves the recursive motive and exact inner frame view required by
--     the handler.
--   * Contains no postulate, hole, permissive option, pre-reveal rotation,
--     broad simulation import, or recursive frame-closing dependency.

import Coercions as C
open import Coercions using (Coercion; Inert; id-onlyᵈ)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpIdFrameClosingDef
  using (PairedLambdaTargetClosingUpIdFrameClosingᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingUpIdFrameWideningCasesDef
  using
    ( PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ
    ; PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ
    )


paired-lambda-target-closing-up-id-frame-widening-cases-proofᵀ :
  PairedLambdaTargetClosingUpIdFrameQuotientIdWideningClosingᵀ →
  PairedLambdaTargetClosingUpIdFrameQuotientCastWideningClosingᵀ →
  PairedLambdaTargetClosingUpIdFrameClosingᵀ
paired-lambda-target-closing-up-id-frame-widening-cases-proofᵀ
    id-closing cast-closing inner view inert-d′ inert-u′ d⊒ d′⊒ qD
    (quotient-id-widening u⊑ u′⊑) r =
  id-closing inner view inert-d′ inert-u′ d⊒ d′⊒ qD u⊑ u′⊑ r
paired-lambda-target-closing-up-id-frame-widening-cases-proofᵀ
    id-closing cast-closing inner view inert-d′ inert-u′ d⊒ d′⊒ qD
    (quotient-cast-widening mode seal u⊑ mode′ seal′ u′⊑) r =
  cast-closing inner view inert-d′ inert-u′ d⊒ d′⊒ qD
    mode seal u⊑ mode′ seal′ u′⊑ r


paired-lambda-target-closing-up-id-frame-handler-proofᵀ :
  PairedLambdaTargetClosingUpIdFrameClosingᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ D D′ B B′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion} →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    M M′ C C′ pC →
  PairedLambdaTargetClosingFrameView ρ
    M M′ (`∀ C) C′ pC →
  Inert d′ → Inert u′ →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ C.`∀ d ∶ `∀ C ⊒ `∀ D →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ d′ ∶ C′ ⊒ D′ →
  (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
  (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
  PairedLambdaTargetClosingFrameClosingMotive ρ
    ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)
    ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) B B′ q
paired-lambda-target-closing-up-id-frame-handler-proofᵀ
    closing inner view inert-d′ inert-u′ d⊒ d′⊒ qD widening q =
  closing inner view inert-d′ inert-u′ d⊒ d′⊒ qD widening q
