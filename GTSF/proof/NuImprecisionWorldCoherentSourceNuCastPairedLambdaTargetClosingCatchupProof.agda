module
  proof.NuImprecisionWorldCoherentSourceNuCastPairedLambdaTargetClosingCatchupProof
  where

-- File Charter:
--   * Removes the administrative post-allocation `β-Λ•` step from direct
--     paired source-`ν ★` target-binder closing.
--   * Delegates only semantic target closing through the runtime widening to
--     one explicit theorem dependency.
--   * Contains no recursive dispatcher, postulate, or permissive option.

open import
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingWidenCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingWidenCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceNuCastPairedLambdaTargetClosingCatchupDef
  using (WorldCoherentSourceNuCastPairedLambdaTargetClosingCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentLeftCatchupPrependKeepStep
  using
    ( post-allocation-β-Λ-cast
    ; world-coherent-left-catchup-prepend-keep-step
    )


world-coherent-source-νcast-paired-lambda-target-closing-catchup-proofᵀ :
  WorldCoherentPairedLambdaTargetClosingWidenCatchupᵀ →
  WorldCoherentSourceNuCastPairedLambdaTargetClosingCatchupᵀ
world-coherent-source-νcast-paired-lambda-target-closing-catchup-proofᵀ
    closing-widen coherent exclusive wfL mode seal★ s⊑ liftν lift∀
    vW noW vW′ noW′ W⊑W′ =
  world-coherent-left-catchup-prepend-keep-step
    (post-allocation-β-Λ-cast vW)
    (closing-widen coherent exclusive wfL mode seal★ s⊑ liftν lift∀
      vW noW vW′ noW′ W⊑W′)
