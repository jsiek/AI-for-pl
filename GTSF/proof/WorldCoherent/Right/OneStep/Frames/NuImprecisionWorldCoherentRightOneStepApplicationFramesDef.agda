module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepApplicationFramesDef
  where

-- File Charter:
--   * Defines the two application evaluation-context frames for
--     target-oriented world-coherent one-step simulation.
--   * Retains successor-world coherence and source-name exclusivity on every
--     continuing related branch.
--   * Contains no implementation, recursion, postulate, hole, or permissive
--     option.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( StoreChange
  ; applyTerm
  )
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; _·_
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


record WorldCoherentRightOneStepApplicationFrames : Set₁ where
  field
    rightStepApplicationLeftFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {L L₁′ M M′ : Term} {A A′ B B′ : Ty}
        {χ : StoreChange}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      No• M →
      No• M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = L} {N′ = L₁′}
        {A = A ⇒ B} {B = A′ ⇒ B′}
        {χ = χ} {ρ = ρ} (pA ↦ pB) →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = L · M} {N′ = L₁′ · applyTerm χ M′}
        {A = B} {B = B′} {χ = χ} {ρ = ρ} pB

    rightStepApplicationRightFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {L L′ M M₁′ : Term} {A A′ B B′ : Ty}
        {χ : StoreChange}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      Value L →
      No• L →
      Value L′ →
      No• L′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ L ⊑ L′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M₁′}
        {A = A} {B = A′} {χ = χ} {ρ = ρ} pA →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = L · M} {N′ = applyTerm χ L′ · M₁′}
        {A = B} {B = B′} {χ = χ} {ρ = ρ} pB

open WorldCoherentRightOneStepApplicationFrames public
