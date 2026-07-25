module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueSynchronizationLemma
  where

-- File Charter:
--   * Exposes the canonical quotient active-value synchronization
--     dispatcher.
--   * Keeps the smaller target-root record explicit for later
--     source-administration inhabitants.
--   * Contains no implementation beyond the Proof-module wrapper, no
--     postulate, hole, permissive option, recursion, or ordinary paired-cast
--     case.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueRootsDef
  using (WorldCoherentRightOneStepQuotientActiveValueRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepQuotientActiveValueSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueSynchronizationProof
  using
  (world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ)


world-coherent-right-one-step-quotient-active-value-synchronizationᵀ :
  WorldCoherentRightOneStepQuotientActiveValueRoots →
  WorldCoherentRightOneStepQuotientActiveValueSynchronizationᵀ
world-coherent-right-one-step-quotient-active-value-synchronizationᵀ =
  world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ
