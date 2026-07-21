module
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupLemma
  where

-- File Charter:
--   * Assembles general source primitive-delta catch-up from the right-value
--     engine and the completed canonical source leaves.
--   * Exposes the remaining right-value dependency explicitly rather than
--     importing an unfinished implementation.
--   * Contains no postulate, hole, permissive option, or broad DGG import.

open import proof.NuImprecisionSourceOneStepDeltaRootLemma using
  (world-coherent-source-delta-rootᵀ)
open import proof.NuImprecisionSourceSilentCompositionLemma using
  (source-silent-compositionᵀ)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesLemma
  using (world-coherent-source-one-step-target-cast-frames)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupCasesDef
  using (WorldCoherentSourcePrimitiveDeltaCatchupCases)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupDef
  using (WorldCoherentSourcePrimitiveDeltaCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupDispatcherProof
  using
  (world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaDirectProof
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
