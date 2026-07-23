module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingDef
  where

-- File Charter:
--   * Defines inert target-cast framing for strong right-value catch-up.
--   * Shares one boundary across reveal, conceal, narrowing, widening, and
--     identity-mode widening evidence.
--   * Leaves active-root reduction and resumed normalization outside this
--     mechanically compositional layer.
--   * Contains no implementation, recursion, postulate, hole, or option.

open import Coercions using
  ( Coercion
  ; Inert
  ; id-onlyᵈ
  )
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightTargetInertFramingᵀ : Set₁
WorldCoherentRightTargetInertFramingᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A A′ B′ : Ty} {c : Coercion}
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
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
