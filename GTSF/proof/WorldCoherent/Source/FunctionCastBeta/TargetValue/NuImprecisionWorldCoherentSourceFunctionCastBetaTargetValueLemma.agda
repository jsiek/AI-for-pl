module
  proof.WorldCoherent.Source.FunctionCastBeta.TargetValue.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueLemma
  where

-- File Charter:
--   * Assembles the source function-cast beta value/value terminal from
--     right-value catch-up and the two paired value leaves.
--   * Supplies the ranked target-function-cast scheduler canonically.
--   * Contains no semantic leaf implementation, postulate, hole, or
--     permissive option.

open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedValues)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetValue.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueDef
  using (WorldCoherentSourceFunctionCastBetaTargetValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetValue.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueSCCProof
  using
  (world-coherent-source-function-cast-beta-target-values-scc-proofᵀ)


world-coherent-source-function-cast-beta-target-valuesᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceFunctionCastBetaPairedValues →
  WorldCoherentSourceFunctionCastBetaTargetValuesᵀ
world-coherent-source-function-cast-beta-target-valuesᵀ =
  world-coherent-source-function-cast-beta-target-values-scc-proofᵀ
