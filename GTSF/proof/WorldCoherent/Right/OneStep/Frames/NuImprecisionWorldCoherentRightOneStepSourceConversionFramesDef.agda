module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesDef
  where

-- File Charter:
--   * Defines source reveal and conceal conversion frames around a
--     target-oriented world-coherent one-step simulation.
--   * Retains the exact left replacement square required by QTI.
--   * Contains no implementation, recursion, postulate, hole, or permissive
--     option.

open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  )
open import ConversionIndexCompatibility using (_[_↦_]ᴸ_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using (StoreChange)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
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


record WorldCoherentRightOneStepSourceConversionFrames : Set₁ where
  field
    rightStepSourceRevealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A B B′ : Ty} {c μ α X}
        {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
      p [ α ↦ X ]ᴸ q →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′} {A = A} {B = B′}
        {χ = χ} {ρ = ρ} p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M ⟨ c ⟩} {N′ = M′} {A = B} {B = B′}
        {χ = χ} {ρ = ρ} q

    rightStepSourceConcealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A B B′ : Ty} {c μ α X}
        {χ : StoreChange}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
      q [ α ↦ X ]ᴸ p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′} {A = A} {B = B′}
        {χ = χ} {ρ = ρ} p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M ⟨ c ⟩} {N′ = M′} {A = B} {B = B′}
        {χ = χ} {ρ = ρ} q

open WorldCoherentRightOneStepSourceConversionFrames public
