module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetNuFramesDef
  where

-- File Charter:
--   * Defines ordinary and casted target-ν frames for a completed source
--     step.
--   * Preserves the existing complete continuing result directly; the
--     recursive join handles source blame without another outcome wrapper.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility alias.

open import Coercions using (Coercion; instᵈ)
import CastImprecisionShape as CastShape
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  ; ⇑ᴿᵢ
  )
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using (StoreChange)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; ν)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; WfTy; ★; `∀; ⟰ᵗ; ⇑ᵗ)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (⊑-target-lift-rightᵢ)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


record WorldCoherentSourceOneStepTargetNuFrames : Set₁ where
  field
    sourceStepTargetNuFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A B B′ C′ : Ty}
        {s : Coercion} {μ} {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WfTy Δᴿ A →
      RevealConversion μ (suc Δᴿ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ₀))
        zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
      (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
      r [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = B} {B = `∀ C′} {χ = χ} {ρ = ρ⁺} q →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = ν A M′ s} {L = L}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} p

    sourceStepTargetNuCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {B B′ C′ : Ty}
        {s : Coercion} {μ} {χ : StoreChange}
        {s-shape : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀)) →
      instᵈ μ ∣ suc Δᴿ
        ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ₀)
        ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
      (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
      CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
      ⌊ r ⌋ ； s-shape ≋ ⌊ p ⌋ →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = B} {B = `∀ C′} {χ = χ} {ρ = ρ⁺} q →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = ν ★ M′ s} {L = L}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} p

open WorldCoherentSourceOneStepTargetNuFrames public
