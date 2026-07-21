module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationSourceAllConcealFrameDef
  where

-- File Charter:
--   * Defines the source universal-conceal continuation frame obligation for
--     paired-lambda target closing.
--   * States the recursive continuation premise and its exact inner frame
--     view explicitly.
--   * Contains no proof, postulate, hole, permissive option, or broad handler
--     import.

import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  )
open import Conversion using (ConcealConversion)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( Term
  ; _⟨_⟩
  )
open import Types using
  ( Ty
  ; TyCtx
  ; TyVar
  ; `∀
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationSourceAllConcealFrameᵀ : Set₁
PairedLambdaTargetClosingContinuationSourceAllConcealFrameᵀ =
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {W W′ : Term} {B C B′ X : Ty}
      {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
      {c : Coercion} {μ : ModeEnv} {α : TyVar} →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ
    W W′ (`∀ B) B′ q →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ)
    α X (C.`∀ c) (`∀ B) (`∀ C) →
  (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    (W ⟨ C.`∀ c ⟩) W′ C B′ r
