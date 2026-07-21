module
  proof.NuImprecisionPairedLambdaTargetClosingContinuationUpIdFrameDef
  where

-- File Charter:
--   * Defines the complete continuation-indexed quotient up-id frame
--     contract as a standalone theorem statement.
--   * Retains the recursive continuation motive and exact proof-relevant
--     inner frame view from the continuation-handler boundary.
--   * Contains no handler projection, implementation, postulate, hole,
--     permissive option, or broad simulation import.

import Coercions as C
open import Coercions using (Coercion; Inert; id-onlyᵈ)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using (QuotientWideningPair)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrameView)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPendingTargetFramesDef
  using (PairedLambdaTargetClosingFrameClosingMotiveᴷ)


PairedLambdaTargetClosingContinuationUpIdFrameᵀ : Set₁
PairedLambdaTargetClosingContinuationUpIdFrameᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ D D′ B B′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ `∀ C ⊑ C′ ⊣ Δᴿ}
    {d d′ u u′ : Coercion} →
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
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
  PairedLambdaTargetClosingFrameClosingMotiveᴷ ρ
    ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)
    ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) B B′ q
