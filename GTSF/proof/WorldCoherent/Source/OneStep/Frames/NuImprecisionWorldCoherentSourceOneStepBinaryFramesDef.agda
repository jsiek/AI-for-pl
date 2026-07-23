module
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepBinaryFramesDef
  where

-- File Charter:
--   * Defines exact aligned application and primitive frames for a completed
--     source step.
--   * Each field consumes and returns the existing complete continuing result;
--     scheduling and source-blame propagation remain outside this record.
--   * Contains no outcome carrier, implementation, recursion, postulate, hole,
--     permissive option, or compatibility wrapper.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; idι
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
  ; _⊕[_]_
  )
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
  ; ‵_
  ; `ℕ
  )
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


record WorldCoherentSourceOneStepBinaryFrames : Set₁ where
  field
    sourceStepApplicationLeftFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {L L′ L₁ M M′ : Term} {A A′ B B′ : Ty}
        {χ : StoreChange}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      No• M →
      No• M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
      WorldCoherentSourceOneStepIndexedResult
        {M = L} {M′ = L′} {L = L₁}
        {A = A ⇒ B} {B = A′ ⇒ B′}
        {χ = χ} {ρ = ρ} (pA ↦ pB) →
      WorldCoherentSourceOneStepIndexedResult
        {M = L · M} {M′ = L′ · M′}
        {L = L₁ · applyTerm χ M}
        {A = B} {B = B′} {χ = χ} {ρ = ρ} pB

    sourceStepApplicationRightFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {V V′ M M′ M₁ : Term} {A A′ B B′ : Ty}
        {χ : StoreChange}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      Value V →
      No• V →
      Value V′ →
      No• V′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ V′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = M₁}
        {A = A} {B = A′} {χ = χ} {ρ = ρ} pA →
      WorldCoherentSourceOneStepIndexedResult
        {M = V · M} {M′ = V′ · M′}
        {L = applyTerm χ V · M₁}
        {A = B} {B = B′} {χ = χ} {ρ = ρ} pB

    sourceStepPrimitiveLeftFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {L L′ L₁ M M′ : Term} {χ : StoreChange} →
      No• M →
      No• M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
      WorldCoherentSourceOneStepIndexedResult
        {M = L} {M′ = L′} {L = L₁}
        {A = ‵ `ℕ} {B = ‵ `ℕ}
        {χ = χ} {ρ = ρ} idι →
      WorldCoherentSourceOneStepIndexedResult
        {M = L ⊕[ addℕ ] M}
        {M′ = L′ ⊕[ addℕ ] M′}
        {L = L₁ ⊕[ addℕ ] applyTerm χ M}
        {A = ‵ `ℕ} {B = ‵ `ℕ}
        {χ = χ} {ρ = ρ} idι

    sourceStepPrimitiveRightFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {V V′ M M′ M₁ : Term} {χ : StoreChange} →
      Value V →
      No• V →
      Value V′ →
      No• V′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ V ⊑ V′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
      WorldCoherentSourceOneStepIndexedResult
        {M = M} {M′ = M′} {L = M₁}
        {A = ‵ `ℕ} {B = ‵ `ℕ}
        {χ = χ} {ρ = ρ} idι →
      WorldCoherentSourceOneStepIndexedResult
        {M = V ⊕[ addℕ ] M}
        {M′ = V′ ⊕[ addℕ ] M′}
        {L = applyTerm χ V ⊕[ addℕ ] M₁}
        {A = ‵ `ℕ} {B = ‵ `ℕ}
        {χ = χ} {ρ = ρ} idι

open WorldCoherentSourceOneStepBinaryFrames public
