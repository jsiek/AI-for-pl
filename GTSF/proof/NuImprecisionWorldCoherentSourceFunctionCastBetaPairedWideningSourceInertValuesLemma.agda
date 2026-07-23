module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesLemma
  where

-- File Charter:
--   * Assembles the world-coherent source-inert paired-widening beta leaf
--     from its pure beta-distributed term-imprecision relation.
--   * Contains no implementation, postulate, hole, or permissive option.

open import
  proof.NuImprecisionSourceFunctionCastBetaPairedWideningSourceInertRelationDef
  using
  (SourceFunctionCastBetaPairedWideningSourceInertRelationᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesDef
  using
  (WorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesProof
  using
  (world-coherent-source-function-cast-beta-paired-widening-source-inert-values-proofᵀ)


world-coherent-source-function-cast-beta-paired-widening-source-inert-valuesᵀ :
  SourceFunctionCastBetaPairedWideningSourceInertRelationᵀ →
  WorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesᵀ
world-coherent-source-function-cast-beta-paired-widening-source-inert-valuesᵀ =
  world-coherent-source-function-cast-beta-paired-widening-source-inert-values-proofᵀ
