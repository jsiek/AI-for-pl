module
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastPairedIndexCatchupProof
  where

-- File Charter:
--   * Reduces paired-index exact-final source-`ν ★` catch-up to a worker on
--     classified polymorphic endpoint values.
--   * Performs only canonical-form inversion; the `AllView` cross-product is
--     retained as one explicit strict theorem dependency.
--   * Contains no recursive dispatcher, canonical assembly, or permissive
--     option.

open import QuotientedTermImprecision using
  (nu-term-imprecision-target-typing)
open import TermTyping using (forget)
open import proof.Source.Core.NuImprecisionSourcePolymorphicValueBase using
  (left-polymorphic-value-shapeᵀ)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastPairedIndexCatchupDef
  using (WorldCoherentFinalSourceNuCastPairedIndexCatchupᵀ)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastPairedIndexViewCatchupDef
  using (WorldCoherentFinalSourceNuCastPairedIndexViewCatchupᵀ)
open import proof.DGG.Core.NuProgress using (canonical-∀)


world-coherent-final-source-νcast-paired-index-catchup-proofᵀ :
  WorldCoherentFinalSourceNuCastPairedIndexViewCatchupᵀ →
  WorldCoherentFinalSourceNuCastPairedIndexCatchupᵀ
world-coherent-final-source-νcast-paired-index-catchup-proofᵀ
    view-catchup coherent exclusive wfL mode seal★ s⊑
    vL noL vV′ noV′ L⊑V′ =
  view-catchup coherent exclusive wfL mode seal★ s⊑
    vL noL vV′ noV′ source-view target-view L⊑V′
  where
  source-view = left-polymorphic-value-shapeᵀ vL L⊑V′

  target-view = canonical-∀ vV′
    (forget (nu-term-imprecision-target-typing L⊑V′))
