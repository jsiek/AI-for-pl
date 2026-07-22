module proof.NuImprecisionWorldCoherentRightValueCatchupCasesDef where

-- File Charter:
--   * Assembles the eight major semantic capabilities used by recursive
--     world-coherent right-value catch-up.
--   * Keeps each independently provable capability in its canonical Def file.
--   * Contains no dispatcher, implementation, compatibility re-export,
--     postulate, hole, or permissive option.

open import proof.NuImprecisionWorldCoherentRightPairedCastFrameDef using
  (WorldCoherentRightPairedCastFrameᵀ)
open import
  proof.NuImprecisionWorldCoherentRightQuotientDownUpFrameDef
  using (WorldCoherentRightQuotientDownUpFrame)
open import proof.NuImprecisionWorldCoherentRightSourceAllClosingDef using
  (WorldCoherentRightSourceAllClosingᵀ)
open import proof.NuImprecisionWorldCoherentRightSourceFramesDef using
  (WorldCoherentRightSourceFrames)
open import
  proof.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (WorldCoherentRightTargetAllocationFrames)
open import
  proof.NuImprecisionWorldCoherentRightTargetBulletClosingDef
  using (WorldCoherentRightTargetBulletClosingᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using (WorldCoherentRightTargetCastTerminalization)
open import proof.NuImprecisionWorldCoherentRightValueTerminalDef using
  (WorldCoherentRightValueTerminalᵀ)


record WorldCoherentRightValueCatchupCases : Set₁ where
  field
    rightValueTerminalCase : WorldCoherentRightValueTerminalᵀ
    rightValueSourceFramesCase : WorldCoherentRightSourceFrames
    rightValueTargetCastTerminalizationCase :
      WorldCoherentRightTargetCastTerminalization
    rightValuePairedCastFrameCase : WorldCoherentRightPairedCastFrameᵀ
    rightValueQuotientDownUpFrameCase :
      WorldCoherentRightQuotientDownUpFrame
    rightValueSourceAllClosingCase : WorldCoherentRightSourceAllClosingᵀ
    rightValueTargetBulletClosingCase :
      WorldCoherentRightTargetBulletClosingᵀ
    rightValueTargetAllocationFramesCase :
      WorldCoherentRightTargetAllocationFrames

open WorldCoherentRightValueCatchupCases public
