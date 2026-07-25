module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepPrimitiveFramesProof
  where

-- File Charter:
--   * Implements the two target-oriented world-coherent primitive frames.
--   * Reuses the exact generic primitive frame builders and preserves the
--     inner successor-world witnesses definitionally.
--   * Contains no recursive dispatcher, postulate, hole, or permissive option.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; idι
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
open import proof.OneStep.NuImprecisionOneStepPrimitiveFrames using
  ( weak-one-step-⊕₁-indexed-frame-relatedᵀ
  ; weak-one-step-⊕₁-source-blame-frameᵀ
  ; weak-one-step-⊕₂-indexed-frame-relatedᵀ
  ; weak-one-step-⊕₂-source-blame-frameᵀ
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepPrimitiveFramesDef
  using (WorldCoherentRightOneStepPrimitiveFrames)

world-coherent-right-one-step-primitive-frames-proofᵀ :
  WorldCoherentRightOneStepPrimitiveFrames
world-coherent-right-one-step-primitive-frames-proofᵀ =
  record
    { rightStepPrimitiveLeftFrame = left-frame
    ; rightStepPrimitiveRightFrame = right-frame
    }
  where
  left-frame :
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
  left-frame noM noM′ M⊑M′
      (world-indexed-outcome-related
        inner coherent exclusive unique) =
    world-indexed-outcome-related
      (weak-one-step-⊕₁-indexed-frame-relatedᵀ
        noM noM′ M⊑M′ inner)
      coherent exclusive unique
  left-frame noM noM′ M⊑M′
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame
      (weak-one-step-⊕₁-source-blame-frameᵀ noM source↠)

  right-frame :
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
  right-frame vL noL vL′ noL′ L⊑L′
      (world-indexed-outcome-related
        inner coherent exclusive unique) =
    world-indexed-outcome-related
      (weak-one-step-⊕₂-indexed-frame-relatedᵀ
        vL noL vL′ noL′ L⊑L′ inner)
      coherent exclusive unique
  right-frame vL noL vL′ noL′ L⊑L′
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame
      (weak-one-step-⊕₂-source-blame-frameᵀ vL noL source↠)
