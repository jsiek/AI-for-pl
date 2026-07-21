module
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllWidenCatchupProof
  where

-- File Charter:
--   * Derives the source polymorphic canonical view required by structural
--     universal-widening target closing.
--   * Delegates the complete fused semantic obligation unchanged to one
--     source-view theorem dependency.
--   * Contains no target-body classification, intermediate index, postulate,
--     or permissive option.

open import proof.NuImprecisionSourcePolymorphicValueBase using
  (left-polymorphic-value-shapeᵀ)
open import
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllWidenCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingAllWidenCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllWidenCatchupSourceViewDef
  using
    (WorldCoherentPairedLambdaTargetClosingAllWidenCatchupSourceViewᵀ)


world-coherent-paired-lambda-target-closing-all-widen-catchup-proofᵀ :
  WorldCoherentPairedLambdaTargetClosingAllWidenCatchupSourceViewᵀ →
  WorldCoherentPairedLambdaTargetClosingAllWidenCatchupᵀ
world-coherent-paired-lambda-target-closing-all-widen-catchup-proofᵀ
    source-view coherent exclusive wfL mode seal★ c⊑ liftν lift∀
    vW noW vW′ noW′ W⊑W′ =
  source-view coherent exclusive wfL mode seal★ c⊑ liftν lift∀
    vW noW vW′ noW′
    (left-polymorphic-value-shapeᵀ vW W⊑W′)
    W⊑W′
