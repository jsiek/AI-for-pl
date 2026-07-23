module
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootCasesLemma
  where

-- File Charter:
--   * Assembles source application pure-root cases from lambda scheduling and
--     the source function-cast beta value/value terminal.
--   * Supplies synchronized ordinary beta from the canonical substitution
--     lemma and shares right-value catch-up across both beta schedulers.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using (WorldCoherentSourceApplicationPureRootCases)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectLemma
  using (world-coherent-source-function-cast-beta-directᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingLemma
  using (world-coherent-source-function-cast-beta-schedulingᵀ)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingDef
  using (WorldCoherentSourceLambdaBetaSchedulingᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaLemma
  using (world-coherent-source-synchronized-lambda-beta-lemmaᵀ)


world-coherent-source-application-pure-root-cases-lemmaᵀ :
  WorldCoherentSourceLambdaBetaSchedulingᵀ →
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ →
  WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ →
  WorldCoherentSourceApplicationPureRootCases
world-coherent-source-application-pure-root-cases-lemmaᵀ
    schedule-lambda right-catchup paired-widening paired-quotient =
  record
    { sourceLambdaBetaRootCase =
        schedule-lambda
          world-coherent-source-synchronized-lambda-beta-lemmaᵀ
    ; sourceFunctionCastBetaRootCase =
        world-coherent-source-function-cast-beta-schedulingᵀ
          (world-coherent-source-function-cast-beta-directᵀ
            right-catchup paired-widening paired-quotient)
    }
