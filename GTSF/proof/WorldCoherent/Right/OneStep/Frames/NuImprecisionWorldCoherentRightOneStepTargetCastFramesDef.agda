module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetCastFramesDef
  where

-- File Charter:
--   * Defines the three target-cast context frames around a target-oriented
--     world-coherent one-step simulation.
--   * Retains the exact cast shape and composition triangle required by QTI.
--   * Excludes active cast roots, recursion, postulates, holes, and permissive
--     options.

open import CastImprecisionShape using (_⊢ᶜ_⦂_)
import CastImprecisionShape as CastShape using (narrowing; widening)
open import Coercions using (id-onlyᵈ)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; _；_≋_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( StoreChange
  ; applyCoercion
  )
open import NuTermImprecision using
  ( StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using
  ( Term
  ; _⟨_⟩
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


record WorldCoherentRightOneStepTargetCastFrames : Set₁ where
  field
    rightStepTargetNarrowCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A A′ B′ : Ty} {c′} {μ′}
        {χ : StoreChange} {s}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
      CastShape.narrowing ⊢ᶜ c′ ⦂ s →
      ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′} {A = A} {B = A′}
        {χ = χ} {ρ = ρ} p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′ ⟨ applyCoercion χ c′ ⟩}
        {A = A} {B = B′} {χ = χ} {ρ = ρ} q

    rightStepTargetWidenCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A A′ B′ : Ty} {c′} {μ′}
        {χ : StoreChange} {s}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
      CastShape.widening ⊢ᶜ c′ ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′} {A = A} {B = A′}
        {χ = χ} {ρ = ρ} p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′ ⟨ applyCoercion χ c′ ⟩}
        {A = A} {B = B′} {χ = χ} {ρ = ρ} q

    rightStepTargetWidenIdCastFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A A′ B′ : Ty} {c′}
        {χ : StoreChange} {s}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
      id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
      CastShape.widening ⊢ᶜ c′ ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′} {A = A} {B = A′}
        {χ = χ} {ρ = ρ} p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′ ⟨ applyCoercion χ c′ ⟩}
        {A = A} {B = B′} {χ = χ} {ρ = ρ} q

open WorldCoherentRightOneStepTargetCastFrames public
