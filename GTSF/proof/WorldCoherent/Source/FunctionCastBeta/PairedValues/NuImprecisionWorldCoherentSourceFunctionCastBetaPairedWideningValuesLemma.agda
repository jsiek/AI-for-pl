module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesLemma
  where

-- File Charter:
--   * Assembles the paired-widening value theorem from its hereditary
--     function-compatible semantic capability.
--   * Exposes no additional compatibility case or result carrier.
--   * Contains no implementation, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesDef
  using
  (WorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesProof
  using
  (world-coherent-source-function-cast-beta-paired-widening-values-proofᵀ)


world-coherent-source-function-cast-beta-paired-widening-valuesᵀ :
  WorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesᵀ →
  WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ
world-coherent-source-function-cast-beta-paired-widening-valuesᵀ =
  world-coherent-source-function-cast-beta-paired-widening-values-proofᵀ
