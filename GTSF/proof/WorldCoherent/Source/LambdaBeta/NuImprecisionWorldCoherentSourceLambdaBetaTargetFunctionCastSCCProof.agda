module
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastSCCProof
  where

-- File Charter:
--   * Closes the direct/value target function-cast scheduling cycle by
--     structural recursion on the exact function-cast spine rank.
--   * Builds the value scheduler at rank `n + 1` from the direct scheduler at
--     rank `n`, then builds the direct scheduler at rank `n + 1`.
--   * Exposes only the existing unranked scheduling statements and contains
--     no postulate, hole, termination pragma, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import proof.Source.Core.NuImprecisionSourceSilentCompositionLemma using
  (source-silent-compositionᵀ)
open import proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef using
  (targetFunctionCastSpineRank)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastDirectProof
  using
  (world-coherent-source-lambda-beta-target-function-cast-direct-at-proofᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastRankedDef
  using
  ( WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ
  ; WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ
  )
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastValueDef
  using (WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ)
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetFunctionCastValueProof
  renaming
  ( world-coherent-source-lambda-beta-target-function-cast-value-suc-at-proofᵀ
      to value-suc-at-proofᵀ
  )
open import
  proof.WorldCoherent.Source.LambdaBeta.NuImprecisionWorldCoherentSourceLambdaBetaTargetLambdaDirectProof
  using
  (world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ)
open import
  proof.WorldCoherent.Source.OneStep.Frames.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesLemma
  using (world-coherent-source-one-step-target-cast-frames)
open import
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  using (WorldCoherentSourceSynchronizedLambdaBetaᵀ)
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependLemma
  using (world-coherent-source-target-keep-prependᵀ)


private
  target-function-cast-direct-at-zero :
    WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ zero
  target-function-cast-direct-at-zero
      prefix coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW ()

  target-function-cast-value-at-zero :
    WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ zero
  target-function-cast-value-at-zero
      prefix coherent exclusive unique wfR okM okM′
      function-related argument-related vV vW vV′ ()

  target-function-cast-schedulers-at :
    WorldCoherentRightValueCatchupPrefixᵀ →
    WorldCoherentSourceSynchronizedLambdaBetaᵀ →
    ∀ n →
    WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ n ×
    WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ n
  target-function-cast-schedulers-at right-catchup synchronized zero =
    target-function-cast-direct-at-zero ,
    target-function-cast-value-at-zero
  target-function-cast-schedulers-at right-catchup synchronized (suc n)
      with target-function-cast-schedulers-at
        right-catchup synchronized n
  target-function-cast-schedulers-at right-catchup synchronized (suc n)
      | direct-previous , value-previous =
    direct-current , value-current
    where
    target-lambda =
      world-coherent-source-lambda-beta-target-lambda-direct-proofᵀ
        right-catchup source-silent-compositionᵀ synchronized

    value-current :
      WorldCoherentSourceLambdaBetaTargetFunctionCastValueAtᵀ (suc n)
    value-current =
      value-suc-at-proofᵀ
        target-lambda direct-previous
        world-coherent-source-one-step-target-cast-frames
        world-coherent-source-target-keep-prependᵀ

    direct-current :
      WorldCoherentSourceLambdaBetaTargetFunctionCastDirectAtᵀ (suc n)
    direct-current =
      world-coherent-source-lambda-beta-target-function-cast-direct-at-proofᵀ
        right-catchup source-silent-compositionᵀ value-current


world-coherent-source-lambda-beta-target-function-cast-direct-scc-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceSynchronizedLambdaBetaᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastDirectᵀ
world-coherent-source-lambda-beta-target-function-cast-direct-scc-proofᵀ
    right-catchup synchronized
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW =
  proj₁
    (target-function-cast-schedulers-at right-catchup synchronized
      (suc (targetFunctionCastSpineRank vW)))
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW refl


world-coherent-source-lambda-beta-target-function-cast-value-scc-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourceSynchronizedLambdaBetaᵀ →
  WorldCoherentSourceLambdaBetaTargetFunctionCastValueᵀ
world-coherent-source-lambda-beta-target-function-cast-value-scc-proofᵀ
    right-catchup synchronized
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vV′ =
  proj₂
    (target-function-cast-schedulers-at right-catchup synchronized
      (suc (targetFunctionCastSpineRank vW)))
    prefix coherent exclusive unique wfR okM okM′
    function-related argument-related vV vW vV′ refl
