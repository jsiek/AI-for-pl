module
  proof.NuImprecisionWorldCoherentSourceOneStepSourceCastFramesDef
  where

-- File Charter:
--   * Defines source cast/conversion framing for a completed recursive source
--     one-step result.
--   * Preserves the target tail and all strong invariants while framing the
--     exact source step with its transported coercion.
--   * Contains no recursive worker, implementation, postulate, hole, or
--     permissive option.

open import Coercions using (Coercion)
open import Conversion using (ConcealConversion; RevealConversion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuReduction using (StoreChange; applyCoercion)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


record WorldCoherentSourceOneStepSourceCastFrames : Set₁ where
  field
    sourceStepSourceNarrowFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A B B′ : Ty}
        {c : Coercion} {μ} {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊒ B →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M ⟨ c ⟩} {M′ = M′}
        {L = L ⟨ applyCoercion χ c ⟩}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q

    sourceStepSourceWidenFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A B B′ : Ty}
        {c : Coercion} {μ} {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ₀) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M ⟨ c ⟩} {M′ = M′}
        {L = L ⟨ applyCoercion χ c ⟩}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q

    sourceStepSourceRevealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A B B′ : Ty}
        {c : Coercion} {μ α X} {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M ⟨ c ⟩} {M′ = M′}
        {L = L ⟨ applyCoercion χ c ⟩}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q

    sourceStepSourceConcealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ L : Term} {A B B′ : Ty}
        {c : Coercion} {μ α X} {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = L}
        {A = A} {B = B′} {χ = χ} {ρ = ρ⁺} p →
      WorldCoherentSourceOneStepIndexedResult
        {M = M ⟨ c ⟩} {M′ = M′}
        {L = L ⟨ applyCoercion χ c ⟩}
        {A = B} {B = B′} {χ = χ} {ρ = ρ⁺} q

open WorldCoherentSourceOneStepSourceCastFrames public
