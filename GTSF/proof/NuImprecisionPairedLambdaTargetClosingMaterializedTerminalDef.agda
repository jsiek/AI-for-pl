module
  proof.NuImprecisionPairedLambdaTargetClosingMaterializedTerminalDef
  where

-- File Charter:
--   * Defines common terminal closing for related universal source values
--     after all pending target frames have been materialized.
--   * The intended proof dispatches on the final `ν` or `∀ⁱ` imprecision
--     index and delegates to the corresponding terminal theorem.
--   * Contains no implementation, postulate, hole, permissive option,
--     continuation, semantic handler, frame view, or broad simulation import.

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
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersDef
  using (PairedLambdaTargetClosingFrameClosingMotive)


PairedLambdaTargetClosingMaterializedTerminalᵀ : Set₁
PairedLambdaTargetClosingMaterializedTerminalᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ} →
  Value W → No• W →
  Value W′ → No• W′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ `∀ F ⊑ B′ ∶ q →
  PairedLambdaTargetClosingFrameClosingMotive
    ρ W W′ F B′ q
