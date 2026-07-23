module
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingCasesDef
  where

-- File Charter:
--   * Collects the flat semantic capabilities used by exhaustive
--     source-universal right-value closing.
--   * Reuses canonical theorem boundaries for terminal, prefix, source-frame,
--     target-frame, and residual cases.
--   * This is a capability record, not a result, view, outcome, or recursive
--     plan hierarchy.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, compatibility re-export, or broad simulation import.

open import
  proof.Right.SourceAll.Frames.NuImprecisionRightSourceAllAllocationPrefixDef
  using (WorldCoherentRightSourceAllAllocationPrefixᵀ)
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingTerminalDef
  using (WorldCoherentRightSourceAllClosingTerminalᵀ)
open import
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllResidualCasesDef
  using (WorldCoherentRightSourceAllResidualCases)
open import
  proof.Right.SourceAll.Frames.NuImprecisionRightSourceAllSourceFramesDef
  using (WorldCoherentRightSourceAllSourceFrames)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetConcealFrameDef
  using (WorldCoherentRightSourceAllTargetConcealFrameᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetIdWidenFrameDef
  using (WorldCoherentRightSourceAllTargetIdWidenFrameᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetNarrowFrameDef
  using (WorldCoherentRightSourceAllTargetNarrowFrameᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetRevealFrameDef
  using (WorldCoherentRightSourceAllTargetRevealFrameᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetWidenFrameDef
  using (WorldCoherentRightSourceAllTargetWidenFrameᵀ)


record WorldCoherentRightSourceAllClosingCases : Set₁ where
  field
    sourceAllTerminalCase :
      WorldCoherentRightSourceAllClosingTerminalᵀ
    sourceAllAllocationPrefixCase :
      WorldCoherentRightSourceAllAllocationPrefixᵀ
    sourceAllSourceFramesCase :
      WorldCoherentRightSourceAllSourceFrames
    sourceAllTargetNarrowFrameCase :
      WorldCoherentRightSourceAllTargetNarrowFrameᵀ
    sourceAllTargetWidenFrameCase :
      WorldCoherentRightSourceAllTargetWidenFrameᵀ
    sourceAllTargetIdWidenFrameCase :
      WorldCoherentRightSourceAllTargetIdWidenFrameᵀ
    sourceAllTargetRevealFrameCase :
      WorldCoherentRightSourceAllTargetRevealFrameᵀ
    sourceAllTargetConcealFrameCase :
      WorldCoherentRightSourceAllTargetConcealFrameᵀ
    sourceAllResidualCases :
      WorldCoherentRightSourceAllResidualCases

open WorldCoherentRightSourceAllClosingCases public
