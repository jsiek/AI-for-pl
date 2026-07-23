module
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingCasesProof
  where

-- File Charter:
--   * Assembles the flat source-universal closing case record.
--   * Makes the recursive closing hypothesis, source-frame leaves, residual
--     leaves, and target terminalization dependency explicit.
--   * Contains no recursive knot, semantic leaf implementation, result/view
--     type, postulate, hole, permissive option, or broad simulation import.

open import
  proof.Right.SourceAll.Frames.NuImprecisionRightSourceAllAllocationPrefixProof
  using (world-coherent-right-source-all-allocation-prefix-proofᵀ)
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingCasesDef
  using (WorldCoherentRightSourceAllClosingCases)
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingTerminalLemma
  using (world-coherent-right-source-all-closing-terminalᵀ)
open import
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllResidualCasesDef
  using (WorldCoherentRightSourceAllResidualCases)
open import
  proof.Right.SourceAll.Frames.NuImprecisionRightSourceAllSourceFramesDef
  using (WorldCoherentRightSourceAllSourceFrames)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetConcealFrameProof
  using
  (world-coherent-right-source-all-target-conceal-frame-proofᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetIdWidenFrameProof
  using
  (world-coherent-right-source-all-target-id-widen-frame-proofᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetNarrowFrameProof
  using
  (world-coherent-right-source-all-target-narrow-frame-proofᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetRevealFrameProof
  using
  (world-coherent-right-source-all-target-reveal-frame-proofᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetWidenFrameProof
  using
  (world-coherent-right-source-all-target-widen-frame-proofᵀ)
open import
  proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingDef
  using (WorldCoherentRightSourceAllClosingᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using (WorldCoherentRightTargetCastTerminalization)


world-coherent-right-source-all-closing-cases-proof :
  WorldCoherentRightSourceAllClosingᵀ →
  WorldCoherentRightSourceAllSourceFrames →
  WorldCoherentRightSourceAllResidualCases →
  WorldCoherentRightTargetCastTerminalization →
  WorldCoherentRightSourceAllClosingCases
world-coherent-right-source-all-closing-cases-proof
    close source-frames residual target-frames = record
  { sourceAllTerminalCase =
      world-coherent-right-source-all-closing-terminalᵀ
  ; sourceAllAllocationPrefixCase =
      world-coherent-right-source-all-allocation-prefix-proofᵀ close
  ; sourceAllSourceFramesCase = source-frames
  ; sourceAllTargetNarrowFrameCase =
      world-coherent-right-source-all-target-narrow-frame-proofᵀ
        close target-frames
  ; sourceAllTargetWidenFrameCase =
      world-coherent-right-source-all-target-widen-frame-proofᵀ
        close target-frames
  ; sourceAllTargetIdWidenFrameCase =
      world-coherent-right-source-all-target-id-widen-frame-proofᵀ
        close target-frames
  ; sourceAllTargetRevealFrameCase =
      world-coherent-right-source-all-target-reveal-frame-proofᵀ
        close target-frames
  ; sourceAllTargetConcealFrameCase =
      world-coherent-right-source-all-target-conceal-frame-proofᵀ
        close target-frames
  ; sourceAllResidualCases = residual
  }
