module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationFromViewDef
  where

-- File Charter:
--   * Defines direct continuation closing from one proof-relevant paired-
--     lambda target-closing frame view.
--   * This is the small public replacement for the thirteen-handler record:
--     the view supplies endpoint value/no-bullet facts and its exact outer
--     quotiented relation.
--   * Contains no implementation, postulate, hole, permissive option,
--     semantic handler, continuation interpreter, or broad simulation import.

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationFromViewᵀ : Set₁
PairedLambdaTargetClosingContinuationFromViewᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameView
    ρ W W′ (`∀ F) B′ q →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ
    ρ W W′ F B′ q
