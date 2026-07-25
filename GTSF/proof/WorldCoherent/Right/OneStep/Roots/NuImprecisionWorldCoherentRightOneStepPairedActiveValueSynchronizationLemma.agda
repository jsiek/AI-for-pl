module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationLemma
  where

-- File Charter:
--   * Exposes the canonical paired active-value synchronization dispatcher.
--   * Keeps the smaller target-root record explicit for later
--     source-administration inhabitants.
--   * Contains no implementation beyond the Proof-module wrapper, no
--     postulate, hole, permissive option, recursion, or quotient case.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueRootsDef
  using (WorldCoherentRightOneStepPairedActiveValueRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationProof
  using
  (world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ)


world-coherent-right-one-step-paired-active-value-synchronizationᵀ :
  WorldCoherentRightOneStepPairedActiveValueRoots →
  WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ
world-coherent-right-one-step-paired-active-value-synchronizationᵀ =
  world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
