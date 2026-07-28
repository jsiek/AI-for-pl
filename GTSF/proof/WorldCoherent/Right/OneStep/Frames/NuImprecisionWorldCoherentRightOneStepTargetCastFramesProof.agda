module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetCastFramesProof
  where

-- File Charter:
--   * Implements the three target-cast context frames for target-oriented
--     world-coherent one-step simulation.
--   * Uses exact related-result frame builders so successor coherence and
--     source-name exclusivity remain definitionally unchanged.
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
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
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
open import proof.OneStep.NuImprecisionOneStepTargetCastFrames using
  ( weak-one-step-target-narrow-cast-indexed-frame-relatedᵀ
  ; weak-one-step-target-widen-cast-indexed-frame-relatedᵀ
  ; weak-one-step-target-widen-id-cast-indexed-frame-relatedᵀ
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
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepTargetCastFramesDef
  using (WorldCoherentRightOneStepTargetCastFrames)

world-coherent-right-one-step-target-cast-frames-proofᵀ :
  WorldCoherentRightOneStepTargetCastFrames
world-coherent-right-one-step-target-cast-frames-proofᵀ =
  record
    { rightStepTargetNarrowCastFrame = narrow-frame
    ; rightStepTargetWidenCastFrame = widen-frame
    ; rightStepTargetWidenIdCastFrame = id-widen-frame
    }
  where
  narrow-frame :
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
  narrow-frame mode seal★ c′⊒ c-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique) =
    world-indexed-outcome-related
      (weak-one-step-target-narrow-cast-indexed-frame-relatedᵀ
        mode seal★ c′⊒ inner _ c-shape comp)
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
  narrow-frame mode seal★ c′⊒ c-shape comp
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame source↠

  widen-frame :
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
  widen-frame mode seal★ c′⊑ c-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique) =
    world-indexed-outcome-related
      (weak-one-step-target-widen-cast-indexed-frame-relatedᵀ
        mode seal★ c′⊑ inner _ c-shape comp)
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
  widen-frame mode seal★ c′⊑ c-shape comp
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame source↠

  id-widen-frame :
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
  id-widen-frame seal★ c′⊑ c-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique) =
    world-indexed-outcome-related
      (weak-one-step-target-widen-id-cast-indexed-frame-relatedᵀ
        seal★ c′⊑ inner _ c-shape comp)
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
  id-widen-frame seal★ c′⊑ c-shape comp
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame source↠
