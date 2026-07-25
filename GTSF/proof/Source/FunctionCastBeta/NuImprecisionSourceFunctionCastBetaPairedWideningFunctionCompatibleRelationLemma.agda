module
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationLemma
  where

-- File Charter:
--   * Exposes canonical paired-widening beta distribution from hereditary
--     function-codomain compatibility.
--   * Contains no implementation, postulate, hole, or permissive option.

open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationDef
  using
  (SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningFunctionCompatibleRelationProof
  using
  (source-function-cast-beta-paired-widening-function-compatible-relation-proofᵀ)


source-function-cast-beta-paired-widening-function-compatible-relationᵀ :
  SourceFunctionCastBetaPairedWideningFunctionCompatibleRelationᵀ
source-function-cast-beta-paired-widening-function-compatible-relationᵀ =
  source-function-cast-beta-paired-widening-function-compatible-relation-proofᵀ
