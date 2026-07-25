module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationLemma
  where

-- File Charter:
--   * Exposes the canonical QTIP target-down active synchronization
--     dispatcher.
--   * Keeps the smaller target-root record explicit for later
--     source-administration inhabitants.
--   * Contains no implementation beyond the Proof-module wrapper, no
--     postulate, hole, permissive option, recursion, or application case.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveRootsDef
  using (WorldCoherentRightOneStepQuotientDownActiveRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationDef
  using (WorldCoherentRightOneStepQuotientDownActiveSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationProof
  using
  (world-coherent-right-one-step-quotient-down-active-synchronization-proofᵀ)


world-coherent-right-one-step-quotient-down-active-synchronizationᵀ :
  WorldCoherentRightOneStepQuotientDownActiveRoots →
  WorldCoherentRightOneStepQuotientDownActiveSynchronizationᵀ
world-coherent-right-one-step-quotient-down-active-synchronizationᵀ =
  world-coherent-right-one-step-quotient-down-active-synchronization-proofᵀ
