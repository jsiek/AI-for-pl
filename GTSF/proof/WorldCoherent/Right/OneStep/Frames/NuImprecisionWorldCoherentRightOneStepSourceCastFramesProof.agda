module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesProof
  where

-- File Charter:
--   * Implements source cast frames for target-oriented world-coherent
--     one-step simulation.
--   * Uses the exact checked indexed cast frames and lifts source blame through
--     the surrounding cast.
--   * Contains no recursive dispatcher, postulate, hole, or permissive option.

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
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-source-narrow-cast-indexed-frameᵀ
  ; weak-one-step-source-widen-cast-indexed-frameᵀ
  )
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepSourceCastFramesDef
  using (WorldCoherentRightOneStepSourceCastFrames)

world-coherent-right-one-step-source-cast-frames-proofᵀ :
  WorldCoherentRightOneStepSourceCastFrames
world-coherent-right-one-step-source-cast-frames-proofᵀ =
  record
    { rightStepSourceNarrowFrame = narrow-frame
    ; rightStepSourceWidenFrame = widen-frame
    }
  where
  narrow-frame :
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
  narrow-frame mode seal★ c⊒ c-shape comp
      (world-indexed-outcome-related
        inner coherent exclusive unique) =
    world-indexed-outcome-related
      (weak-one-step-source-narrow-cast-indexed-frameᵀ
        mode seal★ c⊒ c-shape comp inner)
      coherent exclusive unique
  narrow-frame mode seal★ c⊒ c-shape comp
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame (cast-blame-tailᵀ source↠)

  widen-frame :
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
  widen-frame mode seal★ c⊑ c-shape comp
      (world-indexed-outcome-related
        inner coherent exclusive unique) =
    world-indexed-outcome-related
      (weak-one-step-source-widen-cast-indexed-frameᵀ
        mode seal★ c⊑ c-shape comp inner)
      coherent exclusive unique
  widen-frame mode seal★ c⊑ c-shape comp
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame (cast-blame-tailᵀ source↠)
