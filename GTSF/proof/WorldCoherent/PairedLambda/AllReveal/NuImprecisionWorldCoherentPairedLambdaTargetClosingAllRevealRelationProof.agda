module
  proof.WorldCoherent.PairedLambda.AllReveal.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllRevealRelationProof
  where

-- File Charter:
--   * Derives the source polymorphic canonical view required by structural
--     `reveal-all` target-closing relation transport.
--   * Delegates the complete fused relation obligation unchanged to one
--     source-view theorem dependency.
--   * Contains no target view, intermediate index, postulate, or permissive
--     option.

open import proof.Source.Core.NuImprecisionSourcePolymorphicValueBase using
  (left-polymorphic-value-shapeᵀ)
open import
  proof.WorldCoherent.PairedLambda.AllReveal.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllRevealRelationDef
  using (WorldCoherentPairedLambdaTargetClosingAllRevealRelationᵀ)
open import
  proof.WorldCoherent.PairedLambda.AllReveal.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllRevealRelationSourceViewDef
  using
    (WorldCoherentPairedLambdaTargetClosingAllRevealRelationSourceViewᵀ)


world-coherent-paired-lambda-target-closing-all-reveal-relation-proofᵀ :
  WorldCoherentPairedLambdaTargetClosingAllRevealRelationSourceViewᵀ →
  WorldCoherentPairedLambdaTargetClosingAllRevealRelationᵀ
world-coherent-paired-lambda-target-closing-all-reveal-relation-proofᵀ
    source-view h⇑A inner liftν lift∀
    vW noW vW′ noW′ W⊑W′ =
  source-view h⇑A inner liftν lift∀
    vW noW vW′ noW′
    (left-polymorphic-value-shapeᵀ vW W⊑W′)
    W⊑W′
