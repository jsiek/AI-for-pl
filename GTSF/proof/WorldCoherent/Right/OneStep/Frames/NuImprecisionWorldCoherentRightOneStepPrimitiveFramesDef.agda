module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepPrimitiveFramesDef
  where

-- File Charter:
--   * Defines the two primitive evaluation-context frames for target-oriented
--     world-coherent one-step simulation.
--   * Retains successor-world coherence and source-name exclusivity on every
--     continuing related branch.
--   * Contains no implementation, recursion, postulate, hole, or permissive
--     option.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; idι
  )
open import NuReduction using
  ( StoreChange
  ; applyTerm
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; _⊕[_]_
  )
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( TyCtx
  ; ‵_
  ; `ℕ
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


record WorldCoherentRightOneStepPrimitiveFrames : Set₁ where
  field
    rightStepPrimitiveLeftFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {L L₁′ M M′ : Term} {χ : StoreChange} →
      No• M →
      No• M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = L} {N′ = L₁′} {A = ‵ `ℕ} {B = ‵ `ℕ}
        {χ = χ} {ρ = ρ} idι →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = L ⊕[ addℕ ] M}
        {N′ = L₁′ ⊕[ addℕ ] applyTerm χ M′}
        {A = ‵ `ℕ} {B = ‵ `ℕ} {χ = χ} {ρ = ρ} idι

    rightStepPrimitiveRightFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {L L′ M M₁′ : Term} {χ : StoreChange} →
      Value L →
      No• L →
      Value L′ →
      No• L′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = M₁′} {A = ‵ `ℕ} {B = ‵ `ℕ}
        {χ = χ} {ρ = ρ} idι →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = L ⊕[ addℕ ] M}
        {N′ = applyTerm χ L′ ⊕[ addℕ ] M₁′}
        {A = ‵ `ℕ} {B = ‵ `ℕ} {χ = χ} {ρ = ρ} idι

open WorldCoherentRightOneStepPrimitiveFrames public
