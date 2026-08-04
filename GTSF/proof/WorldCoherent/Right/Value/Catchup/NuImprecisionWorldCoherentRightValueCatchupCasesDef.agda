module proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupCasesDef where

-- File Charter:
--   * Assembles the eight major semantic capability families used by recursive
--     world-coherent right-value catch-up.
--   * Keeps the three live paired constructor cases explicit in their family.
--   * Contains no dispatcher, implementation, compatibility re-export,
--     postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightPairedFramesDef
  using (WorldCoherentRightPairedFramesᵀ)
open import
  proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightQuotientDownUpFrameDef
  using (WorldCoherentRightQuotientDownUpFrame)
open import proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingDef using
  (WorldCoherentRightSourceAllClosingᵀ)
open import proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceFramesDef using
  (WorldCoherentRightSourceFrames)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetAllocationFramesDef
  using (WorldCoherentRightTargetAllocationFrames)
open import
  proof.WorldCoherent.Right.Target.Other.NuImprecisionWorldCoherentRightTargetBulletClosingDef
  using (WorldCoherentRightTargetBulletClosingᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using (WorldCoherentRightTargetCastTerminalization)
open import proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalDef using
  (WorldCoherentRightValueTerminalᵀ)


record WorldCoherentRightValueCatchupCases : Set₁ where
  field
    rightValueTerminalCase : WorldCoherentRightValueTerminalᵀ
    rightValueSourceFramesCase : WorldCoherentRightSourceFrames
    rightValueTargetCastTerminalizationCase :
      WorldCoherentRightTargetCastTerminalization
    rightValuePairedFrames : WorldCoherentRightPairedFramesᵀ
    rightValueQuotientDownUpFrameCase :
      WorldCoherentRightQuotientDownUpFrame
    rightValueSourceAllClosingCase : WorldCoherentRightSourceAllClosingᵀ
    rightValueTargetBulletClosingCase :
      WorldCoherentRightTargetBulletClosingᵀ
    rightValueTargetAllocationFramesCase :
      WorldCoherentRightTargetAllocationFrames

open WorldCoherentRightValueCatchupCases public
