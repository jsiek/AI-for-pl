module
  proof.NuImprecisionRightSourceAllClosingCasesProof
  where

-- File Charter:
--   * Assembles the flat source-universal closing case record.
--   * Makes the recursive closing hypothesis, source-frame leaves, residual
--     leaves, and target terminalization dependency explicit.
--   * Contains no recursive knot, semantic leaf implementation, result/view
--     type, postulate, hole, permissive option, or broad simulation import.

open import
  proof.NuImprecisionRightSourceAllAllocationPrefixProof
  using (world-coherent-right-source-all-allocation-prefix-proofᵀ)
open import
  proof.NuImprecisionRightSourceAllClosingCasesDef
  using (WorldCoherentRightSourceAllClosingCases)
open import
  proof.NuImprecisionRightSourceAllClosingTerminalLemma
  using (world-coherent-right-source-all-closing-terminalᵀ)
open import
  proof.NuImprecisionRightSourceAllResidualCasesDef
  using (WorldCoherentRightSourceAllResidualCases)
open import
  proof.NuImprecisionRightSourceAllSourceFramesDef
  using (WorldCoherentRightSourceAllSourceFrames)
open import
  proof.NuImprecisionRightSourceAllTargetConcealFrameProof
  using
  (world-coherent-right-source-all-target-conceal-frame-proofᵀ)
open import
  proof.NuImprecisionRightSourceAllTargetIdWidenFrameProof
  using
  (world-coherent-right-source-all-target-id-widen-frame-proofᵀ)
open import
  proof.NuImprecisionRightSourceAllTargetNarrowFrameProof
  using
  (world-coherent-right-source-all-target-narrow-frame-proofᵀ)
open import
  proof.NuImprecisionRightSourceAllTargetRevealFrameProof
  using
  (world-coherent-right-source-all-target-reveal-frame-proofᵀ)
open import
  proof.NuImprecisionRightSourceAllTargetWidenFrameProof
  using
  (world-coherent-right-source-all-target-widen-frame-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentRightSourceAllClosingDef
  using (WorldCoherentRightSourceAllClosingᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
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
