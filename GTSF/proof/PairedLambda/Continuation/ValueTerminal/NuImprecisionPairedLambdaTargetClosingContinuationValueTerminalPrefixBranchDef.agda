module
  proof.PairedLambda.Continuation.ValueTerminal.NuImprecisionPairedLambdaTargetClosingContinuationValueTerminalPrefixBranchDef
  where

-- File Charter:
--   * Defines closure of the continuation-indexed paired-lambda terminal
--     motive under one relational-store allocation prefix.
--   * Receives the already-computed recursive result, keeping structural
--     recursion visible at the eventual direct QTI proof site.
--   * Contains no implementation, QTI recursion, terminal theorem, postulate,
--     hole, permissive option, materialization, or broad simulation import.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.PairedLambda.Terminal.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationValueTerminalPrefixBranchᵀ : Set₁
PairedLambdaTargetClosingContinuationValueTerminalPrefixBranchᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {F B′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ F ⊑ B′ ⊣ Δᴿ} →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ
    ρ₀ W W′ F B′ q →
  StoreImpPrefix ρ₀ ρ →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ W ⦂ `∀ F →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ W′ ⦂ B′ →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ
    ρ W W′ F B′ q
