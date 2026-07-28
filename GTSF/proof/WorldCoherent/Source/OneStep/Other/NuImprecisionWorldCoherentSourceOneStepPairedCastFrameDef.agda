module
  proof.WorldCoherent.Source.OneStep.Other.NuImprecisionWorldCoherentSourceOneStepPairedCastFrameDef
  where

-- File Charter:
--   * Defines exact paired reveal, conceal, and widening framing for one
--     completed source step.
--   * Carries the evidence of the corresponding live term-imprecision
--     constructor directly.
--   * Contains no retired paired-cast carrier, outcome wrapper,
--     implementation, recursion, postulate, hole, permissive option, or
--     compatibility alias.

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion; ModeEnv)
open import Conversion using
  (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import ImprecisionComposition using
  (ImprecisionShape; _；_≋_; ⌊_⌋)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuReduction using (StoreChange; applyCoercion)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import QuotientImprecisionCompatibility using
  (ReductionClosedPairedWideningCompatible)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; TyVar)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


record WorldCoherentSourceOneStepPairedCastFrameᵀ : Set₁ where
  field
    sourceStepPairedRevealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A A′ B B′ X X′ : Ty}
        {c c′ : Coercion} {α β : TyVar} {μ μ′ : ModeEnv}
        {χ : StoreChange}
        {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      StoreCorresponds ρ₀ α X β X′ pX →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ₀)
        β X′ c′ A′ B′ →
      p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M ⟨ c ⟩} {M′ = M′ ⟨ c′ ⟩}
        {L = L ⟨ applyCoercion χ c ⟩}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q

    sourceStepPairedConcealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A A′ B B′ X X′ : Ty}
        {c c′ : Coercion} {α β : TyVar} {μ μ′ : ModeEnv}
        {χ : StoreChange}
        {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      StoreCorresponds ρ₀ α X β X′ pX →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ₀)
        β X′ c′ A′ B′ →
      q [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M ⟨ c ⟩} {M′ = M′ ⟨ c′ ⟩}
        {L = L ⟨ applyCoercion χ c ⟩}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q

    sourceStepPairedWideningFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A A′ B B′ : Ty}
        {c c′ : Coercion} {μ μ′ : ModeEnv}
        {s s′ t : ImprecisionShape} {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
      widening ⊢ᶜ c ⦂ s →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊑ B′ →
      widening ⊢ᶜ c′ ⦂ s′ →
      s ； ⌊ q ⌋ ≋ t →
      ⌊ p ⌋ ； s′ ≋ t →
      ReductionClosedPairedWideningCompatible
        Φ Δᴸ Δᴿ c c′ p q s s′ →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = A′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M ⟨ c ⟩} {M′ = M′ ⟨ c′ ⟩}
        {L = L ⟨ applyCoercion χ c ⟩}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q

open WorldCoherentSourceOneStepPairedCastFrameᵀ public
