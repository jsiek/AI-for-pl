module
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupCasesDef
  where

-- File Charter:
--   * Defines the two dependencies of general source-delta catch-up.
--   * Separates direct two-operand scheduling from structural target frames.
--   * Contains no dispatcher, scheduling proof, postulate, hole, or option.

open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using (WorldCoherentSourceOneStepTargetCastFrames)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaDirectDef
  using (WorldCoherentSourcePrimitiveDeltaDirectᵀ)


record WorldCoherentSourcePrimitiveDeltaCatchupCases : Set₁ where
  field
    sourcePrimitiveDeltaDirectCase :
      WorldCoherentSourcePrimitiveDeltaDirectᵀ

    sourcePrimitiveDeltaTargetCastFrames :
      WorldCoherentSourceOneStepTargetCastFrames

open WorldCoherentSourcePrimitiveDeltaCatchupCases public
