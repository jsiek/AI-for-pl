module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedOuterCastRootsLemma
  where

-- File Charter:
--   * Supplies the canonical paired source-inert and source-active wrappers
--     to the four-field paired outer-cast assembly.
--   * Leaves only ordinary active-value synchronization and the two distinct
--     quotient semantic boundaries explicit.
--   * Contains no dispatcher, postulate, hole, permissive option, or
--     compatibility wrapper.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedOuterCastRootsDef
  using (WorldCoherentRightOneStepPairedOuterCastRoots)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedOuterCastRootsProof
  using (world-coherent-right-one-step-paired-outer-cast-roots-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootLemma
  using (world-coherent-right-one-step-paired-source-active-value-rootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertValueRootLemma
  using (world-coherent-right-one-step-paired-source-inert-value-rootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepQuotientActiveValueSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientFrameRecursionDef
  using (WorldCoherentRightOneStepQuotientFrameRecursionᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-paired-outer-cast-rootsᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ →
  WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ →
  WorldCoherentRightOneStepQuotientFrameRecursionᵀ →
  WorldCoherentRightOneStepQuotientActiveValueSynchronizationᵀ →
  WorldCoherentRightOneStepPairedOuterCastRoots
world-coherent-right-one-step-paired-outer-cast-rootsᵀ
    left-catchup right-catchup runtime-transport paired-active
    quotient-frame quotient-active =
  world-coherent-right-one-step-paired-outer-cast-roots-proofᵀ
    (world-coherent-right-one-step-paired-source-inert-value-rootᵀ
      left-catchup right-catchup runtime-transport)
    (world-coherent-right-one-step-paired-source-active-value-rootᵀ
      left-catchup paired-active)
    quotient-frame quotient-active
