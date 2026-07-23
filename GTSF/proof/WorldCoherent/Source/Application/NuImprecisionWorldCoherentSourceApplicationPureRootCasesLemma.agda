module
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootCasesLemma
  where

-- File Charter:
--   * Assembles source application pure-root cases from lambda scheduling and
--     the source function-cast beta value/value terminal.
--   * Supplies synchronized ordinary beta from the canonical substitution
--     lemma and shares right-value catch-up across both beta schedulers.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Source.Application.NuImprecisionWorldCoherentSourceApplicationPureRootCasesDef
  using (WorldCoherentSourceApplicationPureRootCases)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.Direct.NuImprecisionWorldCoherentSourceFunctionCastBetaDirectLemma
  using (world-coherent-source-function-cast-beta-directᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedQuotientValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.PairedValues.NuImprecisionWorldCoherentSourceFunctionCastBetaPairedWideningValuesDef
  using (WorldCoherentSourceFunctionCastBetaPairedWideningValuesᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.Scheduling.NuImprecisionWorldCoherentSourceFunctionCastBetaSchedulingLemma
  using (world-coherent-source-function-cast-beta-schedulingᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaSchedulingDef
  using (WorldCoherentSourceLambdaBetaSchedulingᵀ)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaLemma
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
