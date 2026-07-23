module proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceRevealCatchupDef where

-- File Charter:
--   * Defines coherent catch-up through one source reveal conversion.
--   * Covers active unseal and inert or administrative reveal forms behind
--     one source-runtime handler contract.
--   * Contains no implementation or recursive dispatcher dependency.

open import Coercions using (Coercion; ModeEnv)
open import Conversion using (RevealConversion)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Types using (Ty; TyCtx; TyVar)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentSourceRevealCatchupᵀ : Set₁
WorldCoherentSourceRevealCatchupᵀ =
  ∀ {Φ} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {N V′ : Term} {A B B′ X : Ty} {c : Coercion}
    {μ : ModeEnv} {α : TyVar}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  Value V′ →
  No• V′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  WorldCoherentLeftCatchupIndexedResult
    {N = N ⟨ c ⟩} {V′ = V′} {ρ = ρ⁺} q
