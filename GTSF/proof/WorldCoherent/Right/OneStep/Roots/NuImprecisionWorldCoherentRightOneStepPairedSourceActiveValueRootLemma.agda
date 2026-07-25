module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootLemma
  where

-- File Charter:
--   * Exposes the arbitrary-inner paired active-source value root while
--     retaining final-value synchronization as the sole semantic dependency.
--   * Supplies source inner-value catch-up explicitly.
--   * Contains no synchronized active-root implementation, quotient case,
--     recursive dispatcher, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootDef
  using (WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootProof
  using
  (world-coherent-right-one-step-paired-source-active-value-root-proofᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-paired-source-active-value-rootᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ →
  WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ
world-coherent-right-one-step-paired-source-active-value-rootᵀ =
  world-coherent-right-one-step-paired-source-active-value-root-proofᵀ
