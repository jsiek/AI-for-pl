module
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingInstWidenCatchupProof
  where

-- File Charter:
--   * Removes the active source `β-inst` step from instantiation widening
--     target closing after one source-only dynamic allocation.
--   * Delegates the fused runtime-`ν ★` allocation and target-closing work to
--     one explicit whole theorem dependency.
--   * Contains no intermediate relation, postulate, or permissive option.

open import NuReduction using (pure-step; β-inst)
open import
  proof.NuImprecisionWorldCoherentLeftCatchupPrependKeepStep
  using (world-coherent-left-catchup-prepend-keep-step)
open import
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingInstPostBetaCatchupDef
  using
    (WorldCoherentPairedLambdaTargetClosingInstPostBetaCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingInstWidenCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingInstWidenCatchupᵀ)


world-coherent-paired-lambda-target-closing-inst-widen-catchup-proofᵀ :
  WorldCoherentPairedLambdaTargetClosingInstPostBetaCatchupᵀ →
  WorldCoherentPairedLambdaTargetClosingInstWidenCatchupᵀ
world-coherent-paired-lambda-target-closing-inst-widen-catchup-proofᵀ
    post-beta coherent exclusive wfL mode seal★ c⊑ liftν lift∀
    vW noW vW′ noW′ W⊑W′ =
  world-coherent-left-catchup-prepend-keep-step
    (pure-step (β-inst vW))
    (post-beta coherent exclusive wfL mode seal★ c⊑ liftν lift∀
      vW noW vW′ noW′ W⊑W′)
