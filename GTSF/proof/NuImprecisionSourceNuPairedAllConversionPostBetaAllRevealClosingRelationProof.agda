module
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationProof
  where

-- File Charter:
--   * Derives structural-all paired-conversion closing from the classified
--     ambient-prefix worker.
--   * Starts the worker at the reflexive prefix after source and target
--     universal canonical-form inversion.
--   * Contains no semantic case analysis, intermediate index, postulate, or
--     permissive option.

open import QuotientedTermImprecision using
  (nu-term-imprecision-target-typing; prefix-reflⁱ)
open import TermTyping using (forget)
open import proof.NuImprecisionSourcePolymorphicValueBase using
  (left-polymorphic-value-shapeᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationDef
  using (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationAmbientViewDef
  using
    (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationAmbientViewᵀ)
open import proof.NuProgress using (canonical-∀)


source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-proofᵀ :
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationAmbientViewᵀ →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ
source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-proofᵀ
    ambient-relation coherent exclusive wfL h⇑A inner liftν lift∀
    vV noV vV′ noV′ conversion V⊑V′ =
  ambient-relation prefix-reflⁱ coherent exclusive wfL h⇑A inner
    liftν lift∀
    vV noV vV′ noV′ source-view target-view conversion V⊑V′
  where
  source-view = left-polymorphic-value-shapeᵀ vV V⊑V′

  target-view = canonical-∀ vV′
    (forget (nu-term-imprecision-target-typing V⊑V′))
