module proof.NuImprecisionWorldCoherentFinalSourceNuCatchupProof where

-- File Charter:
--   * Assembles exact-final ordinary source-`ν` catch-up by the two possible
--     inner universal precision indices.
--   * Keeps source-only allocation and paired-index semantics as explicit
--     whole theorem dependencies.
--   * Contains no allocation implementation, recursive dispatcher, or
--     permissive option.

open import ImprecisionWf using (∀ⁱ_) renaming (ν to νⁱ)
open import proof.NuImprecisionWorldCoherentFinalSourceNuCatchupDef using
  (WorldCoherentFinalSourceNuCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentFinalSourceNuPairedIndexCatchupDef using
  (WorldCoherentFinalSourceNuPairedIndexCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentFinalSourceNuSourceOnlyIndexCatchupDef using
  (WorldCoherentFinalSourceNuSourceOnlyIndexCatchupᵀ)


world-coherent-final-source-ν-catchup-proofᵀ :
  WorldCoherentFinalSourceNuSourceOnlyIndexCatchupᵀ →
  WorldCoherentFinalSourceNuPairedIndexCatchupᵀ →
  WorldCoherentFinalSourceNuCatchupᵀ
world-coherent-final-source-ν-catchup-proofᵀ
    source-only paired {q = νⁱ occ r}
    coherent exclusive wfL hA h⇑A s↑ liftρ liftγ
    vL noL vV′ noV′ L⊑V′ =
  source-only coherent exclusive wfL hA h⇑A s↑ liftρ liftγ
    vL noL vV′ noV′ L⊑V′
world-coherent-final-source-ν-catchup-proofᵀ
    source-only paired {q = ∀ⁱ r}
    coherent exclusive wfL hA h⇑A s↑ liftρ liftγ
    vL noL vV′ noV′ L⊑V′ =
  paired coherent exclusive wfL hA h⇑A s↑ liftρ liftγ
    vL noL vV′ noV′ L⊑V′
