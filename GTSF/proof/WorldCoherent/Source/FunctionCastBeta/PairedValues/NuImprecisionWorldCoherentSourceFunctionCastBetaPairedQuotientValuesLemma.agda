module
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedQuotientValuesLemma
  where

-- File Charter:
--   * Assembles the world-coherent paired-quotient beta leaf from its pure
--     beta-distributed term-imprecision relation.
--   * Contains no implementation, postulate, hole, or permissive option.

open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationDef
  using (SourceFunctionCastBetaPairedQuotientRelationᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedQuotientValuesProof
  using
  (world-coherent-source-function-cast-beta-paired-quotient-values-proofᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using
  (WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ)


world-coherent-source-function-cast-beta-paired-quotient-valuesᵀ :
  SourceFunctionCastBetaPairedQuotientRelationᵀ →
  WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ
world-coherent-source-function-cast-beta-paired-quotient-valuesᵀ =
  world-coherent-source-function-cast-beta-paired-quotient-values-proofᵀ
