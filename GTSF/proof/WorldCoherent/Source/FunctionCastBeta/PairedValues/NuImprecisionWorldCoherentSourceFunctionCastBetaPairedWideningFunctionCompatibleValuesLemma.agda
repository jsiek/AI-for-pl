module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesLemma
  where

-- File Charter:
--   * Assembles the world-coherent function-compatible paired-widening beta
--     leaf from its pure beta-distributed term-imprecision relation.
--   * Contains no implementation, postulate, hole, or permissive option.

open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationDef
  using
  (SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesDef
  using
  (WorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesProof
  using
  (world-coherent-source-function-cast-beta-paired-widening-function-compatible-values-proofᵀ)


world-coherent-source-function-cast-beta-paired-widening-function-compatible-valuesᵀ :
  SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ →
  WorldCoherentSourceFunctionCastBetaPairedWideningFunctionCompatibleValuesᵀ
world-coherent-source-function-cast-beta-paired-widening-function-compatible-valuesᵀ =
  world-coherent-source-function-cast-beta-paired-widening-function-compatible-values-proofᵀ
