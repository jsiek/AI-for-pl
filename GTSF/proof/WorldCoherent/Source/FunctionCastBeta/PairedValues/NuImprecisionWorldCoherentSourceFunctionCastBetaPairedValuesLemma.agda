module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesLemma
  where

-- File Charter:
--   * Assembles the paired source function-cast beta value leaves from the
--     remaining paired-widening and quotient-widening capabilities.
--   * Supplies both paired-conversion function cases canonically.
--   * Contains no semantic leaf implementation, postulate, hole, or
--     permissive option.

open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using
  ( WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ
  ; WorldCoherentSourceFunctionCastBetaPairedValues
  )
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesProof
  using (world-coherent-source-function-cast-beta-paired-values-proofᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ)


world-coherent-source-function-cast-beta-paired-valuesᵀ :
  WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ →
  WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ →
  WorldCoherentSourceFunctionCastBetaPairedValues
world-coherent-source-function-cast-beta-paired-valuesᵀ =
  world-coherent-source-function-cast-beta-paired-values-proofᵀ
