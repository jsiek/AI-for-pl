module
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationProof
  where

-- File Charter:
--   * Derives structural-all paired-conversion closing from the classified
--     canonical-view worker.
--   * Performs only source and target universal canonical-form inversion and
--     retains the fused final relation unchanged.
--   * Contains no semantic case analysis, postulate, or permissive option.

open import QuotientedTermImprecision using
  (nu-term-imprecision-target-typing)
open import TermTyping using (forget)
open import proof.NuImprecisionSourcePolymorphicValueBase using
  (left-polymorphic-value-shapeᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationDef
  using (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ)
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationViewDef
  using (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationViewᵀ)
open import proof.NuProgress using (canonical-∀)


source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-proofᵀ :
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationViewᵀ →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationᵀ
source-ν-paired-all-conversion-post-beta-all-reveal-closing-relation-proofᵀ
    view-relation h⇑A inner liftν lift∀
    vV noV vV′ noV′ conversion V⊑V′ =
  view-relation h⇑A inner liftν lift∀
    vV noV vV′ noV′ source-view target-view conversion V⊑V′
  where
  source-view = left-polymorphic-value-shapeᵀ vV V⊑V′

  target-view = canonical-∀ vV′
    (forget (nu-term-imprecision-target-typing V⊑V′))
