module
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedCastRuntimeSiblingCatchupLemma
  where

-- File Charter:
--   * Canonically assembles exact-final paired-cast runtime-sibling catch-up
--     from the isolated paired-conversion family and paired-widening proof.
--   * Keeps the source-runtime sibling capability as the only semantic input.
--   * Contains no recursive measure, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedCastRuntimeSiblingCatchupDef
  using (WorldCoherentFinalPairedCastRuntimeSiblingCatchupᵀ)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedCastRuntimeSiblingCatchupProof
  using
  (world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ)
open import
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedConversionValueRuntimeSiblingCatchupProof
  using
  (world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ)
open import
  proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceRuntimeSiblingCatchupDef
  using (WorldCoherentSourceRuntimeSiblingCatchupᵀ)


world-coherent-final-paired-cast-runtime-sibling-catchupᵀ :
  WorldCoherentSourceRuntimeSiblingCatchupᵀ →
  WorldCoherentFinalPairedCastRuntimeSiblingCatchupᵀ
world-coherent-final-paired-cast-runtime-sibling-catchupᵀ =
  world-coherent-final-paired-cast-runtime-sibling-catchup-proofᵀ
    world-coherent-final-paired-conversion-value-runtime-sibling-catchup-proofᵀ
