module proof.NuImprecisionWorldCoherentTargetInertFrameCatchupDef where

-- File Charter:
--   * Defines one coherent target-inert-cast framing capability over an
--     already-established indexed left catch-up result.
--   * Keeps reveal, conceal, narrowing, widening, and identity-mode widening
--     evidence as five explicit alternatives in the theorem statement.
--   * Contains no implementation, recursive dispatcher, or permissive option.

open import Coercions using (Coercion; Inert; ModeEnv; id-onlyᵈ)
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_; _∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentTargetInertFrameCatchupᵀ : Set₁
WorldCoherentTargetInertFrameCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M V′ : Term} {A A′ B′ : Ty} {c : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  Inert c →
  ((∃[ μ ] ∃[ β ] ∃[ X′ ]
      RevealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X′ c A′ B′)
   ⊎
   (∃[ μ ] ∃[ β ] ∃[ X′ ]
      ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X′ c A′ B′)
   ⊎
   (∃[ μ ]
      CastMode μ ×
      SealModeStore★ μ (rightStoreⁱ ρ₀) ×
      (μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊒ B′))
   ⊎
   (∃[ μ ]
      CastMode μ ×
      SealModeStore★ μ (rightStoreⁱ ρ₀) ×
      (μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊑ B′))
   ⊎
   (SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) ×
    (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊑ B′))) →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
