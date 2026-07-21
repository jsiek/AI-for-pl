module
  proof.NuImprecisionWorldCoherentFinalSourceNuPairedIndexCatchupProof
  where

-- File Charter:
--   * Proves exact-final ordinary source-`ν` paired-index catch-up from the
--     whole allocation-sensitive worker on classified polymorphic values.
--   * Performs only the source and target canonical-form inversions; the
--     `AllView` cross-product remains an explicit strict theorem dependency.
--   * Contains no recursive dispatcher, canonical assembly, or permissive
--     option.

open import TermTyping using (forget)
open import QuotientedTermImprecision using
  (nu-term-imprecision-target-typing)
open import proof.NuImprecisionSourceBulletBase using
  (left-polymorphic-value-shapeᵀ)
open import
  proof.NuImprecisionWorldCoherentFinalSourceNuPairedIndexCatchupDef using
  (WorldCoherentFinalSourceNuPairedIndexCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentFinalSourceNuPairedIndexViewCatchupDef
  using (WorldCoherentFinalSourceNuPairedIndexViewCatchupᵀ)
open import proof.NuProgress using (canonical-∀)


world-coherent-final-source-ν-paired-index-catchup-proofᵀ :
  WorldCoherentFinalSourceNuPairedIndexViewCatchupᵀ →
  WorldCoherentFinalSourceNuPairedIndexCatchupᵀ
world-coherent-final-source-ν-paired-index-catchup-proofᵀ
    view-catchup coherent exclusive wfL hA h⇑A s↑ liftρ liftγ
    vL noL vV′ noV′ L⊑V′ =
  view-catchup coherent exclusive wfL hA h⇑A s↑ liftρ liftγ
    vL noL vV′ noV′ source-view target-view L⊑V′
  where
  source-view = left-polymorphic-value-shapeᵀ vL L⊑V′

  target-view = canonical-∀ vV′
    (forget (nu-term-imprecision-target-typing L⊑V′))
