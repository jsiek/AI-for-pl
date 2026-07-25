module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesDef
  where

-- File Charter:
--   * Defines source narrowing and widening frames around a target-oriented
--     world-coherent one-step simulation.
--   * Retains the exact cast shape and composition triangle required by QTI.
--   * Contains no implementation, recursion, postulate, hole, or permissive
--     option.

open import CastImprecisionShape using (_⊢ᶜ_⦂_)
import CastImprecisionShape as CastShape using (narrowing; widening)
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
open import NuReduction using (StoreChange)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
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


record WorldCoherentRightOneStepSourceCastFrames : Set₁ where
  field
    rightStepSourceNarrowFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A A′ B : Ty} {c} {μ}
        {χ : StoreChange} {s}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
      CastShape.narrowing ⊢ᶜ c ⦂ s →
      s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′} {A = A} {B = A′}
        {χ = χ} {ρ = ρ} p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M ⟨ c ⟩} {N′ = M′} {A = B} {B = A′}
        {χ = χ} {ρ = ρ} q

    rightStepSourceWidenFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {A A′ B : Ty} {c} {μ}
        {χ : StoreChange} {s}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ} →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
      CastShape.widening ⊢ᶜ c ⦂ s →
      s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M′} {A = A} {B = A′}
        {χ = χ} {ρ = ρ} p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M ⟨ c ⟩} {N′ = M′} {A = B} {B = A′}
        {χ = χ} {ρ = ρ} q

open WorldCoherentRightOneStepSourceCastFrames public
