module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationPairedWideningFrameDef
  where

-- File Charter:
--   * Defines the complete continuation-indexed paired-widening frame
--     contract as a standalone theorem statement.
--   * Retains the recursive continuation motive and exact proof-relevant
--     inner frame view from the continuation-handler boundary.
--   * Contains no handler projection, implementation, postulate, hole,
--     permissive option, or broad simulation import.

import Coercions as C
open import Coercions using (Coercion; Inert; ModeEnv)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; _⟨_⟩)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationPairedWideningFrameᵀ : Set₁
PairedLambdaTargetClosingContinuationPairedWideningFrameᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {B C B′ C′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
    {c c′ : Coercion} {μ μ′ : ModeEnv} →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
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
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    (W ⟨ C.`∀ c ⟩) (W′ ⟨ c′ ⟩) C C′ r
