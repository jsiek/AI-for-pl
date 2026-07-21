module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationSourceAllNarrowingFrameDef
  where

-- File Charter:
--   * Defines the source universal-narrowing continuation frame obligation
--     for paired-lambda target closing.
--   * States the recursive continuation premise and its exact inner frame
--     view explicitly.
--   * Contains no proof, postulate, hole, permissive option, or broad handler
--     import.

import Coercions as C
open import Coercions using
  ( Coercion
  ; ModeEnv
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( Term
  ; _⟨_⟩
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; `∀
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationSourceAllNarrowingFrameᵀ : Set₁
PairedLambdaTargetClosingContinuationSourceAllNarrowingFrameᵀ =
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {W W′ : Term} {B C B′ : Ty}
      {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
      {c : Coercion} {μ : ModeEnv} →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    W W′ B B′ q →
  PairedLambdaTargetClosingFrameView ρ
    W W′ (`∀ B) B′ q →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ C.`∀ c ∶ `∀ B ⊒ `∀ C →
  (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    (W ⟨ C.`∀ c ⟩) W′ C B′ r
