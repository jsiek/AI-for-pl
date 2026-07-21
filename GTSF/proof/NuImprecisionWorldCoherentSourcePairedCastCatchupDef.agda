module proof.NuImprecisionWorldCoherentSourcePairedCastCatchupDef where

-- File Charter:
--   * Defines coherent source catch-up through one paired cast.
--   * Retains the inertness exposed by the target-value constructor.
--   * Contains no accumulated-change transport or terminal implementation.

open import Coercions using (Coercion; Inert)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (PairedCast; StoreImpPrefix)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentSourcePairedCastCatchupᵀ : Set₁
WorldCoherentSourcePairedCastCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ : Term} {A A′ B B′ : Ty} {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  PairedCast Φ Δᴸ Δᴿ ρ₀
    c c′ {A} {A′} {B} {B′} p q →
  Value V′ →
  No• V′ →
  Inert c′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ c ⟩}
    {V′ = V′ ⟨ c′ ⟩}
    {ρ = ρ⁺} q
