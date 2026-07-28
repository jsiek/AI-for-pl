module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationLemma
  where

-- File Charter:
--   * Exposes the canonical paired active-value synchronization dispatcher.
--   * Restricts the exact live paired source-active value-root cells to the
--     final-value synchronization boundary.
--   * Contains no implementation beyond the Proof-module wrapper, no
--     generic paired-cast abstraction, postulate, hole, recursion, or
--     quotient case.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationProof
  using
  (world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootDef
  using (WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ)


world-coherent-right-one-step-paired-active-value-synchronizationᵀ :
  WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ →
  WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ
world-coherent-right-one-step-paired-active-value-synchronizationᵀ =
  world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
