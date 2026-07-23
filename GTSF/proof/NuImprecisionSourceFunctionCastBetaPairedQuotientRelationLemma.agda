module
  proof.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationLemma
  where

-- File Charter:
--   * Assembles quotient-paired function beta distribution from its
--     application-specific quotient capability.
--   * Contains no implementation, postulate, hole, or permissive option.

open import
  proof.NuImprecisionQuotientFunctionPairedNarrowingApplicationDef
  using (QuotientFunctionPairedNarrowingApplicationᵀ)
open import
  proof.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationDef
  using (SourceFunctionCastBetaPairedQuotientRelationᵀ)
open import
  proof.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationProof
  using
  (source-function-cast-beta-paired-quotient-relation-proofᵀ)


source-function-cast-beta-paired-quotient-relationᵀ :
  QuotientFunctionPairedNarrowingApplicationᵀ →
  SourceFunctionCastBetaPairedQuotientRelationᵀ
source-function-cast-beta-paired-quotient-relationᵀ =
  source-function-cast-beta-paired-quotient-relation-proofᵀ
