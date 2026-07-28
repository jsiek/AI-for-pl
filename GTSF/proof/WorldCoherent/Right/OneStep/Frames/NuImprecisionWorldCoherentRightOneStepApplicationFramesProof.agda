module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepApplicationFramesProof
  where

-- File Charter:
--   * Implements the two target-oriented world-coherent application frames.
--   * Reuses the exact generic application frame builders and preserves the
--     inner successor-world witnesses definitionally.
--   * Contains no recursive dispatcher, postulate, hole, or permissive option.

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
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
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
  proof.Catchup.Simulation.NuImprecisionSimulationCore
  using
  ( ·₁-blame-tail
  ; ·₂-blame-tail
  ; weak-indexed-arrow-resultᵀ
  ; weak-one-step-·₁-frame-preserves-transportᵀ
  ; weak-one-step-·₁-frame-preserves-type-coherenceᵀ
  ; weak-one-step-·₁-frameᵀ
  ; weak-one-step-·₂-indexed-frameᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; canonicalArrowResults
  ; relatedResults
  ; transportNo•Terms
  ; weakArrowResult
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
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
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepApplicationFramesDef
  using (WorldCoherentRightOneStepApplicationFrames)

world-coherent-right-one-step-application-frames-proofᵀ :
  WorldCoherentRightOneStepApplicationFrames
world-coherent-right-one-step-application-frames-proofᵀ =
  record
    { rightStepApplicationLeftFrame = left-frame
    ; rightStepApplicationRightFrame = right-frame
    }
  where
  left-frame :
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
  left-frame noM noM′ M⊑M′
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique) =
    world-indexed-outcome-related
      framed
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
    where
    arrow = weak-indexed-arrow-resultᵀ inner
    base = weakArrowResult arrow
    L⊑L′ = canonicalArrowResults arrow
    transported-M =
      transportNo•Terms
        (weakIndexedTransport inner) noM noM′ M⊑M′
    raw =
      weak-one-step-·₁-frameᵀ
        noM noM′ base L⊑L′ transported-M
    framed =
      weak-indexed-result raw (relatedResults raw)
        (weak-one-step-·₁-frame-preserves-transportᵀ
          noM noM′ base L⊑L′ transported-M
          (weakIndexedTransport inner))
        (weak-one-step-·₁-frame-preserves-type-coherenceᵀ
          noM noM′ base L⊑L′ transported-M
          (weakIndexedTypeCoherence inner))
  left-frame noM noM′ M⊑M′
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame (·₁-blame-tail noM source↠)

  right-frame :
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
  right-frame vL noL vL′ noL′ L⊑L′
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique) =
    world-indexed-outcome-related
      (weak-one-step-·₂-indexed-frameᵀ
        vL noL vL′ noL′ L⊑L′ inner
        (weakIndexedTransport inner)
        (weakIndexedTypeCoherence inner))
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
  right-frame vL noL vL′ noL′ L⊑L′
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame (·₂-blame-tail vL noL source↠)
