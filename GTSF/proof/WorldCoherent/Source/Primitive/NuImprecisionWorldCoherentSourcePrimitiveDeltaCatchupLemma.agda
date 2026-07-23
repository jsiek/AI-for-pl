module
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupLemma
  where

-- File Charter:
--   * Assembles general source primitive-delta catch-up from the right-value
--     engine and the completed canonical source leaves.
--   * Exposes the remaining right-value dependency explicitly rather than
--     importing an unfinished implementation.
--   * Contains no postulate, hole, permissive option, or broad DGG import.

open import proof.Source.OneStep.NuImprecisionSourceOneStepDeltaRootLemma using
  (world-coherent-source-delta-rootᵀ)
open import proof.Source.Core.NuImprecisionSourceSilentCompositionLemma using
  (source-silent-compositionᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesLemma
  using (world-coherent-source-one-step-target-cast-frames)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupCasesDef
  using (WorldCoherentSourcePrimitiveDeltaCatchupCases)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupDef
  using (WorldCoherentSourcePrimitiveDeltaCatchupᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupDispatcherProof
  using
  (world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaDirectProof
  using (world-coherent-source-primitive-delta-direct-proofᵀ)


world-coherent-source-primitive-delta-catchupᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourcePrimitiveDeltaCatchupᵀ
world-coherent-source-primitive-delta-catchupᵀ right-catchup =
  world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases
  where
  cases : WorldCoherentSourcePrimitiveDeltaCatchupCases
  cases = record
    { sourcePrimitiveDeltaDirectCase =
        world-coherent-source-primitive-delta-direct-proofᵀ
          right-catchup source-silent-compositionᵀ
          world-coherent-source-delta-rootᵀ
    ; sourcePrimitiveDeltaTargetCastFrames =
        world-coherent-source-one-step-target-cast-frames
    }
