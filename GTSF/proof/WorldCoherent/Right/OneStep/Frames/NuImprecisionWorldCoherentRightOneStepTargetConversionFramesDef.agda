module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetConversionFramesDef
  where

-- File Charter:
--   * Defines target reveal and conceal conversion context frames around a
--     target-oriented world-coherent one-step simulation.
--   * Retains the exact right-index replacement evidence required by QTI.
--   * Excludes active conversion roots, recursion, postulates, holes, and
--     permissive options.

open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  )
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( StoreChange
  ; applyCoercion
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using
  ( Term
  ; _⟨_⟩
  )
open import Types using
  ( Ty
  ; TyCtx
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


record WorldCoherentRightOneStepTargetConversionFrames : Set₁ where
  field
    rightStepTargetRevealConversionFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A A′ B′ : Ty} {c′} {μ′ β X′}
        {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
      p [ β ↦ X′ ]ᴿ q →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′} {A = A} {B = A′}
        {χ = χ} {ρ = ρ} p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′ ⟨ applyCoercion χ c′ ⟩}
        {A = A} {B = B′} {χ = χ} {ρ = ρ} q

    rightStepTargetConcealConversionFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A A′ B′ : Ty} {c′} {μ′ β X′}
        {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
      q [ β ↦ X′ ]ᴿ p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′} {A = A} {B = A′}
        {χ = χ} {ρ = ρ} p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′ ⟨ applyCoercion χ c′ ⟩}
        {A = A} {B = B′} {χ = χ} {ρ = ρ} q

open WorldCoherentRightOneStepTargetConversionFrames public
