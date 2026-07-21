module proof.NuImprecisionWorldCoherentRightPairedCastFrameDef where

-- File Charter:
--   * Defines the world-coherent right paired-cast frame capability.
--   * Keeps paired coercion evidence, runtime/value premises, the recursive
--     result, and the framed indexed result explicit at this boundary.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, compatibility re-export, or broad simulation import.

open import Data.List using ([])

open import Coercions using (Coercion; Inert)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedCast
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightPairedCastFrameᵀ : Set₁
WorldCoherentRightPairedCastFrameᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A A′ B B′ : Ty} {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ c′ ⟩) →
  Value M →
  No• M →
  Inert c →
  PairedCast Φ Δᴸ Δᴿ ρ₀ c c′ p q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = M ⟨ c ⟩} {M′ = M′ ⟨ c′ ⟩} {ρ = ρ⁺} q
