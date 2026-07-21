module proof.NuImprecisionWorldCoherentSourceWidenCatchupDef where

-- File Charter:
--   * Defines world-coherent catch-up for one source widening cast.
--   * Exposes the ambient store prefix and exact final imprecision index.
--   * Contains no implementation or source-runtime record dependency.

open import Coercions using (Coercion; ModeEnv)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentSourceWidenCatchupᵀ : Set₁
WorldCoherentSourceWidenCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ : Term} {A B B′ : Ty} {c : Coercion}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  Value V′ →
  No• V′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q
