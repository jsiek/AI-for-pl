module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesLemma
  where

-- File Charter:
--   * Assembles the paired-widening value theorem from its remaining
--     source-inert semantic capability.
--   * Exposes no additional compatibility case or result carrier.
--   * Contains no implementation, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesDef
  using
  (WorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesProof
  using
  (world-coherent-source-function-cast-beta-paired-widening-values-proofᵀ)


world-coherent-source-function-cast-beta-paired-widening-valuesᵀ :
  WorldCoherentSourceFunctionCastBetaPairedWideningSourceInertValuesᵀ →
  WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ
world-coherent-source-function-cast-beta-paired-widening-valuesᵀ =
  world-coherent-source-function-cast-beta-paired-widening-values-proofᵀ
