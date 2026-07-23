module
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupCasesAssemblyProof
  where

-- File Charter:
--   * Assembles right-value catch-up cases from the flat target-cast
--     terminalization dependencies and the remaining semantic capabilities.
--   * Reuses one target-allocation capability for active target roots and
--     recursive right-value allocation cases.
--   * Returns the existing case record directly and defines no result,
--     outcome, view, alias, compatibility shim, postulate, hole, or option.

open import
  proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightPairedCastFrameDef
  using (WorldCoherentRightPairedCastFrameᵀ)
open import
  proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightQuotientDownUpFrameDef
  using (WorldCoherentRightQuotientDownUpFrame)
open import
  proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingDef
  using (WorldCoherentRightSourceAllClosingᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetActiveRootResumeDef
  using (WorldCoherentRightTargetActiveRootResume)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (WorldCoherentRightTargetAllocationFrames)
open import
  proof.WorldCoherent.Right.Target.Other.NuImprecisionWorldCoherentRightTargetBulletClosingDef
  using (WorldCoherentRightTargetBulletClosingᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationProof
  using (world-coherent-right-target-cast-terminalization-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingProof
  using (world-coherent-right-target-inert-framing-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingSequenceContinuationDef
  using (WorldCoherentRightTargetPendingSequenceContinuation)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupCasesDef
  using (WorldCoherentRightValueCatchupCases)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupCasesProof
  using (world-coherent-right-value-catchup-cases-proofᵀ)


world-coherent-right-value-catchup-cases-from-target-builders-proofᵀ :
  WorldCoherentRightTargetPendingSequenceContinuation →
  WorldCoherentRightTargetActiveRootResume →
  WorldCoherentRightPairedCastFrameᵀ →
  WorldCoherentRightQuotientDownUpFrame →
  WorldCoherentRightSourceAllClosingᵀ →
  WorldCoherentRightTargetBulletClosingᵀ →
  WorldCoherentRightTargetAllocationFrames →
  WorldCoherentRightValueCatchupCases
world-coherent-right-value-catchup-cases-from-target-builders-proofᵀ
    pending roots paired quotient source-all target-bullet allocation =
  world-coherent-right-value-catchup-cases-proofᵀ
    (world-coherent-right-target-cast-terminalization-proofᵀ
      world-coherent-right-target-inert-framing-proofᵀ
      pending roots allocation)
    paired quotient source-all target-bullet allocation
