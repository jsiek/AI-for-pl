module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertValueRootLemma
  where

-- File Charter:
--   * Assembles the paired source-inert value root from the two existing
--     value catch-up capabilities.
--   * Supplies canonical indexed target-step residualization internally.
--   * Contains no active-source synchronization, quotient case, recursive
--     dispatcher, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertValueRootDef
  using (WorldCoherentRightOneStepPairedSourceInertValueRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertValueRootProof
  using
  (world-coherent-right-one-step-paired-source-inert-value-root-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepValueIndexedRootLemma
  using (world-coherent-right-one-step-value-indexed-rootᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-paired-source-inert-value-rootᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ →
  WorldCoherentRightOneStepPairedSourceInertValueRootᵀ
world-coherent-right-one-step-paired-source-inert-value-rootᵀ
    left-catchup right-catchup runtime-transport =
  world-coherent-right-one-step-paired-source-inert-value-root-proofᵀ
    left-catchup
    (world-coherent-right-one-step-value-indexed-rootᵀ
      right-catchup runtime-transport)
