module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalDef
  where

-- File Charter:
--   * Defines common terminal closing for related universal source values
--     under an arbitrary pending target continuation.
--   * The intended proof materializes the continuation and dispatches on its
--     final `ν` or `∀ⁱ` imprecision index.
--   * Contains no implementation, postulate, hole, permissive option,
--     semantic handler, frame view, or broad simulation import.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; Term; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationValueTerminalᵀ : Set₁
PairedLambdaTargetClosingContinuationValueTerminalᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ} →
  Value W → No• W →
  Value W′ → No• W′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ `∀ F ⊑ B′ ∶ q →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ
    ρ W W′ F B′ q
