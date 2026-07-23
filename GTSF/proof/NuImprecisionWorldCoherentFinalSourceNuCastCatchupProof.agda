module proof.NuImprecisionWorldCoherentFinalSourceNuCastCatchupProof where

-- File Charter:
--   * Assembles exact-final source-`ν ★` catch-up by the two possible inner
--     universal precision indices.
--   * Keeps source-only allocation and the paired-index obstruction as
--     explicit whole theorem dependencies.
--   * Contains no allocation implementation, recursive dispatcher, or
--     permissive option.

open import ImprecisionWf using (∀ⁱ_) renaming (ν to νⁱ)
open import proof.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef using
  (WorldCoherentFinalSourceNuCastCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentFinalSourceNuCastPairedIndexCatchupDef
  using (WorldCoherentFinalSourceNuCastPairedIndexCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupDef
  using (WorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupᵀ)


world-coherent-final-source-νcast-catchup-proofᵀ :
  WorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupᵀ →
  WorldCoherentFinalSourceNuCastPairedIndexCatchupᵀ →
  WorldCoherentFinalSourceNuCastCatchupᵀ
world-coherent-final-source-νcast-catchup-proofᵀ
    source-only paired {q = νⁱ safe occ r}
    coherent exclusive wfL mode seal★ s⊑
    vL noL vV′ noV′ L⊑V′ =
  source-only {{safe = safe}}
    coherent exclusive wfL mode seal★ s⊑
    vL noL vV′ noV′ L⊑V′
world-coherent-final-source-νcast-catchup-proofᵀ
    source-only paired {q = ∀ⁱ r}
    coherent exclusive wfL mode seal★ s⊑
    vL noL vV′ noV′ L⊑V′ =
  paired coherent exclusive wfL mode seal★ s⊑
    vL noL vV′ noV′ L⊑V′
