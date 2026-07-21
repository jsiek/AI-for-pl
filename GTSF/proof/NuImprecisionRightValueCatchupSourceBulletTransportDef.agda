module proof.NuImprecisionRightValueCatchupSourceBulletTransportDef where

-- File Charter:
--   * Defines the source-bullet transport invariant retained by completed
--     right-value catch-up results.
--   * Specializes transport to the unique runtime-bullet leaf while keeping
--     the existing weak result as the single success payload.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([])

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyTerm; applyTerms; applyTy; applyTys; keep)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; ⇑ᵗᵐ; _•)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  (_∣_∣_⊢_⦂_)
open import Types using
  (Ty; TyCtx)
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  ; transportType
  )


RightValueCatchupSourceBulletTransportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V N′ : Term} {A A′ : Ty} →
  WeakOneStepResult ρ⁺ V N′ A A′ keep →
  Set₁
RightValueCatchupSourceBulletTransportᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ⁺ = ρ⁺} result =
  ∀ {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
    {L M′ : Term} {C C′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RuntimeOK ((⇑ᵗᵐ L) •) →
  No• M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ []
    ⊢ (⇑ᵗᵐ L) • ⦂ C →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ (⇑ᵗᵐ L) • ⊑ M′ ⦂ C ⊑ C′ ∶ q →
  resultCtx result
    ∣ resultLeftCtx result
    ∣ resultRightCtx result
    ∣ resultStore result ∣ []
    ⊢ᴺ applyTerms
          (sourceChanges result) ((⇑ᵗᵐ L) •)
      ⊑ applyTerms
          (targetTailChanges result)
          (applyTerm keep M′)
    ⦂ applyTys (sourceChanges result) C
      ⊑ applyTys
          (targetTailChanges result)
          (applyTy keep C′)
    ∶ transportType result q
