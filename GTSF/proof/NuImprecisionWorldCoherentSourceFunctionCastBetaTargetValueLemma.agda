module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueLemma
  where

-- File Charter:
--   * Assembles the source function-cast beta value/value terminal from
--     right-value catch-up and the two paired value leaves.
--   * Supplies the ranked target-function-cast scheduler canonically.
--   * Contains no semantic leaf implementation, postulate, hole, or
--     permissive option.

open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedValues)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueDef
  using (WorldCoherentSourceFunctionCastBetaTargetValuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueSCCProof
  using
  (world-coherent-source-function-cast-beta-target-values-scc-proofᵀ)


world-coherent-source-function-cast-beta-target-valuesᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceFunctionCastBetaPairedValues →
  WorldCoherentSourceFunctionCastBetaTargetValuesᵀ
world-coherent-source-function-cast-beta-target-valuesᵀ =
  world-coherent-source-function-cast-beta-target-values-scc-proofᵀ
