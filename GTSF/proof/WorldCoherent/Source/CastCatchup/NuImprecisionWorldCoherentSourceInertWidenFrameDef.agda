module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceInertWidenFrameDef
  where

-- File Charter:
--   * Defines the reusable world-coherent framing contract for one inert
--     source widening.
--   * Keeps the initial-to-ambient store prefix explicit.
--   * Contains no catch-up implementation or recursive semantic dependency.

import Coercions as C
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentSourceInertWidenFrameᵀ : Set₁
WorldCoherentSourceInertWidenFrameᵀ =
  ∀ {Φ Δᴸ Δᴿ} {N V′ : Term} {A B B′ : Ty} {c : C.Coercion}
    {μ : C.ModeEnv}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  C.Inert c →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q
