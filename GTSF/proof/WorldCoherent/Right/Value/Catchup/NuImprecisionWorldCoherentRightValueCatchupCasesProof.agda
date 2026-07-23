module
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupCasesProof
  where

-- File Charter:
--   * Assembles the complete right-value case record from the six unfinished
--     capabilities and the two completed canonical families.
--   * Makes the exact remaining right-value frontier explicit near DGG.
--   * Contains no semantic leaf, postulate, hole, permissive option, or broad
--     DGG import.

open import proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightPairedCastFrameDef using
  (WorldCoherentRightPairedCastFrameᵀ)
open import
  proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightQuotientDownUpFrameDef
  using (WorldCoherentRightQuotientDownUpFrame)
open import proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingDef using
  (WorldCoherentRightSourceAllClosingᵀ)
open import proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceFramesLemma using
  (world-coherent-right-source-frames)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (WorldCoherentRightTargetAllocationFrames)
open import
  proof.WorldCoherent.Right.Target.Other.NuImprecisionWorldCoherentRightTargetBulletClosingDef
  using (WorldCoherentRightTargetBulletClosingᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using (WorldCoherentRightTargetCastTerminalization)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupCasesDef
  using (WorldCoherentRightValueCatchupCases)
open import proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalLemma using
  (world-coherent-right-value-terminalᵀ)


world-coherent-right-value-catchup-cases-proofᵀ :
  WorldCoherentRightTargetCastTerminalization →
  WorldCoherentRightPairedCastFrameᵀ →
  WorldCoherentRightQuotientDownUpFrame →
  WorldCoherentRightSourceAllClosingᵀ →
  WorldCoherentRightTargetBulletClosingᵀ →
  WorldCoherentRightTargetAllocationFrames →
  WorldCoherentRightValueCatchupCases
world-coherent-right-value-catchup-cases-proofᵀ
    target-casts paired-cast quotient source-all target-bullet
    target-allocation =
  record
    { rightValueTerminalCase = world-coherent-right-value-terminalᵀ
    ; rightValueSourceFramesCase = world-coherent-right-source-frames
    ; rightValueTargetCastTerminalizationCase = target-casts
    ; rightValuePairedCastFrameCase = paired-cast
    ; rightValueQuotientDownUpFrameCase = quotient
    ; rightValueSourceAllClosingCase = source-all
    ; rightValueTargetBulletClosingCase = target-bullet
    ; rightValueTargetAllocationFramesCase = target-allocation
    }
