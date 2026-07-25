module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesProof
  where

-- File Charter:
--   * Implements exact source conversion frames for target-oriented
--     world-coherent one-step simulation.
--   * Reuses the checked indexed reveal and conceal frames and preserves the
--     successor-world invariants on related outcomes.
--   * Contains no recursive dispatcher, postulate, hole, or permissive option.

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
  proof.OneStep.NuImprecisionOneStepSourceConversionFrames
  using
  ( weak-one-step-source-conceal-conversion-indexed-frameᵀ
  ; weak-one-step-source-reveal-conversion-indexed-frameᵀ
  )
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ)
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
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceConversionFramesDef
  using (WorldCoherentRightOneStepSourceConversionFrames)

world-coherent-right-one-step-source-conversion-frames-proofᵀ :
  WorldCoherentRightOneStepSourceConversionFrames
world-coherent-right-one-step-source-conversion-frames-proofᵀ =
  record
    { rightStepSourceRevealFrame = reveal-frame
    ; rightStepSourceConcealFrame = conceal-frame
    }
  where
  reveal-frame :
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
  reveal-frame {q = q} c↑ replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      =
    world-indexed-outcome-related
      (weak-one-step-source-reveal-conversion-indexed-frameᵀ
        c↑ inner q replace)
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
  reveal-frame c↑ replace
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame (cast-blame-tailᵀ source↠)

  conceal-frame :
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
  conceal-frame {q = q} c↓ replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      =
    world-indexed-outcome-related
      (weak-one-step-source-conceal-conversion-indexed-frameᵀ
        c↓ inner q replace)
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
  conceal-frame c↓ replace
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame (cast-blame-tailᵀ source↠)
