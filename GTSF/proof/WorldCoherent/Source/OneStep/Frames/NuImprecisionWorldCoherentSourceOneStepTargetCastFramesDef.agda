module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  where

-- File Charter:
--   * Defines target cast/conversion framing for completed source steps.
--   * Preserves the exact source step and final world invariants while
--     extending only the target trace and relation.
--   * Contains no implementation, active target normalization, hole, or
--     permissive option.

open import Coercions using (Coercion; id-onlyᵈ)
import CastImprecisionShape as CastShape
open import Conversion using (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuReduction using (StoreChange)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


record WorldCoherentSourceOneStepTargetCastFrames : Set₁ where
  field
    sourceStepTargetNarrowFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A A′ B′ : Ty}
        {c′ : Coercion} {μ′} {χ : StoreChange}
        {s : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊒ B′ →
      CastShape.narrowing CastShape.⊢ᶜ c′ ⦂ s →
      ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
        {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q

    sourceStepTargetWidenFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A A′ B′ : Ty}
        {c′ : Coercion} {μ′} {χ : StoreChange}
        {s : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊑ B′ →
      CastShape.widening CastShape.⊢ᶜ c′ ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
        {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q

    sourceStepTargetIdWidenFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A A′ B′ : Ty}
        {c′ : Coercion} {χ : StoreChange}
        {s : ImprecisionShape}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ c′ ∶ A′ ⊑ B′ →
      CastShape.widening CastShape.⊢ᶜ c′ ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
        {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q

    sourceStepTargetRevealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A A′ B′ : Ty}
        {c′ : Coercion} {μ′ β X′} {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ₀)
        β X′ c′ A′ B′ →
      p [ β ↦ X′ ]ᴿ q →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
        {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q

    sourceStepTargetConcealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A A′ B′ : Ty}
        {c′ : Coercion} {μ′ β X′} {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ₀)
        β X′ c′ A′ B′ →
      q [ β ↦ X′ ]ᴿ p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′ ⟨ c′ ⟩} {L = L}
        {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} q

open WorldCoherentSourceOneStepTargetCastFrames public
