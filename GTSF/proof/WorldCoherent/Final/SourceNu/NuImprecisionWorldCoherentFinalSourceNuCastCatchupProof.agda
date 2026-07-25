module proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastCatchupProof where

-- File Charter:
--   * Assembles exact-final source-`ν ★` catch-up by the two possible inner
--     universal precision-index body views.
--   * Keeps source-only allocation and the paired-index obstruction as
--     explicit whole theorem dependencies.
--   * Contains no allocation implementation, recursive dispatcher, or
--     permissive option.

open import proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef using
  (WorldCoherentFinalSourceNuCastCatchupᵀ)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastIndexBodyViewDef
  using (paired-index-body; source-only-index-body)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastPairedIndexCatchupDef
  using (WorldCoherentFinalSourceNuCastPairedIndexCatchupᵀ)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupDef
  using (WorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupᵀ)


world-coherent-final-source-νcast-catchup-proofᵀ :
  WorldCoherentFinalSourceNuCastSourceOnlyIndexCatchupᵀ →
  WorldCoherentFinalSourceNuCastPairedIndexCatchupᵀ →
  WorldCoherentFinalSourceNuCastCatchupᵀ
world-coherent-final-source-νcast-catchup-proofᵀ
    source-only paired
    coherent exclusive wfL mode seal★ s⊑
    (source-only-index-body {{safe = safe}} r) s-shape comp
    vL noL vV′ noV′ L⊑V′ =
  source-only {{safe = safe}}
    coherent exclusive wfL mode seal★ s⊑ s-shape comp
    vL noL vV′ noV′ L⊑V′
world-coherent-final-source-νcast-catchup-proofᵀ
    source-only paired
    coherent exclusive wfL mode seal★ s⊑
    (paired-index-body r) s-shape comp
    vL noL vV′ noV′ L⊑V′ =
  paired coherent exclusive wfL mode seal★ s⊑ s-shape comp
    vL noL vV′ noV′ L⊑V′
