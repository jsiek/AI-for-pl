module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetConversionFramesProof
  where

-- File Charter:
--   * Implements target reveal and conceal conversion context frames for
--     target-oriented world-coherent one-step simulation.
--   * Uses exact related-result frame builders so successor coherence and
--     source-name exclusivity remain definitionally unchanged.
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
open import NuTermImprecision using
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
  proof.OneStep.NuImprecisionOneStepTargetConversionFrames
  using
  ( weak-one-step-target-conceal-conversion-indexed-frame-relatedᵀ
  ; weak-one-step-target-reveal-conversion-indexed-frame-relatedᵀ
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetConversionFramesDef
  using (WorldCoherentRightOneStepTargetConversionFrames)

world-coherent-right-one-step-target-conversion-frames-proofᵀ :
  WorldCoherentRightOneStepTargetConversionFrames
world-coherent-right-one-step-target-conversion-frames-proofᵀ =
  record
    { rightStepTargetRevealConversionFrame = reveal-frame
    ; rightStepTargetConcealConversionFrame = conceal-frame
    }
  where
  reveal-frame :
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
  reveal-frame c′↑ replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique) =
    world-indexed-outcome-related
      (weak-one-step-target-reveal-conversion-indexed-frame-relatedᵀ
        c′↑ inner _ replace)
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
  reveal-frame c′↑ replace
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame source↠

  conceal-frame :
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
  conceal-frame c′↓ replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique) =
    world-indexed-outcome-related
      (weak-one-step-target-conceal-conversion-indexed-frame-relatedᵀ
        c′↓ inner _ replace)
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
  conceal-frame c′↓ replace
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame source↠
