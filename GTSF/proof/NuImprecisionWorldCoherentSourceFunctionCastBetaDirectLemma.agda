module
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectLemma
  where

-- File Charter:
--   * Assembles direct source function-cast beta scheduling from right-value
--     catch-up and the single value/value terminal.
--   * Supplies both source-silent composition layers canonically.
--   * Contains no semantic terminal implementation, recursion, postulate,
--     hole, or permissive option.

open import
  proof.NuImprecisionSourceSilentCompositionLemma
  using (source-silent-compositionᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectDef
  using (WorldCoherentSourceFunctionCastBetaDirectᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectProof
  using
  (world-coherent-source-function-cast-beta-direct-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using
  ( WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ
  ; WorldCoherentSourceFunctionCastBetaPairedValues
  )
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesLemma
  using (world-coherent-source-function-cast-beta-paired-valuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueProof
  using
  (world-coherent-source-function-cast-beta-target-value-proofᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetValueLemma
  using (world-coherent-source-function-cast-beta-target-valuesᵀ)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSilentCompositionLemma
  using (world-coherent-source-silent-compositionᵀ)


world-coherent-source-function-cast-beta-directᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ →
  WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ →
  WorldCoherentSourceFunctionCastBetaDirectᵀ
world-coherent-source-function-cast-beta-directᵀ
    right-catchup paired-widening paired-quotient =
  world-coherent-source-function-cast-beta-direct-proofᵀ
    right-catchup world-coherent-source-silent-compositionᵀ
    (world-coherent-source-function-cast-beta-target-value-proofᵀ
      right-catchup source-silent-compositionᵀ
      (world-coherent-source-function-cast-beta-target-valuesᵀ
        right-catchup
        (world-coherent-source-function-cast-beta-paired-valuesᵀ
          paired-widening paired-quotient)))
