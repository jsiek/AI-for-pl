module
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningSourceInertRelationLemma
  where

-- File Charter:
--   * Assembles source-inert paired-widening beta distribution from its
--     application-specific quotient capability.
--   * Contains no implementation, postulate, hole, or permissive option.

open import
  proof.NuCore.Misc.NuImprecisionOrdinaryFunctionPairedNarrowingApplicationDef
  using (OrdinaryFunctionPairedNarrowingApplicationᵀ)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningSourceInertRelationDef
  using
  (SourceFunctionCastBetaPairedWideningSourceInertRelationᵀ)
open import
  proof.Source.FunctionCastBeta.NuImprecisionSourceFunctionCastBetaPairedWideningSourceInertRelationProof
  using
  (source-function-cast-beta-paired-widening-source-inert-relation-proofᵀ)


source-function-cast-beta-paired-widening-source-inert-relationᵀ :
  OrdinaryFunctionPairedNarrowingApplicationᵀ →
  SourceFunctionCastBetaPairedWideningSourceInertRelationᵀ
source-function-cast-beta-paired-widening-source-inert-relationᵀ =
  source-function-cast-beta-paired-widening-source-inert-relation-proofᵀ
