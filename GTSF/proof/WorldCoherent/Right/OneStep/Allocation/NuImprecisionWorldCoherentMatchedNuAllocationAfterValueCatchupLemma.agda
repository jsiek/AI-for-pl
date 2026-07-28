module
  proof.WorldCoherent.Right.OneStep.Allocation.NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupLemma
  where

-- File Charter:
--   * Exposes the canonical world-coherent matched allocation after left
--     value catch-up.
--   * Assembles the lower allocation lemma with the focused world proof.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, or legacy allocation-simulation import.

open import
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationAfterValueCatchupLemma
  using (matched-nu-allocation-after-value-catchupᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Allocation.NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupDef
  using (WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Allocation.NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupProof
  using
  (world-coherent-matched-nu-allocation-after-value-catchup-proofᵀ)


world-coherent-matched-nu-allocation-after-value-catchupᵀ :
  WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ
world-coherent-matched-nu-allocation-after-value-catchupᵀ =
  world-coherent-matched-nu-allocation-after-value-catchup-proofᵀ
    matched-nu-allocation-after-value-catchupᵀ
