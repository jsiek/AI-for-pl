module proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCatchupProof where

-- File Charter:
--   * Assembles exact-final ordinary source-`ν` catch-up from the preserved
--     source-`ν` index view.
--   * Keeps source-only allocation as an explicit whole theorem dependency.
--   * Contains no allocation implementation, recursive dispatcher, or
--     permissive option.

open import Agda.Builtin.Equality using (refl)
open import proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCatchupDef using
  (WorldCoherentFinalSourceNuCatchupᵀ)
open import
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuSourceOnlyIndexCatchupDef using
  (WorldCoherentFinalSourceNuSourceOnlyIndexCatchupᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  (SourceNuIndex; source-nu-index)


world-coherent-final-source-ν-catchup-proofᵀ :
  WorldCoherentFinalSourceNuSourceOnlyIndexCatchupᵀ →
  WorldCoherentFinalSourceNuCatchupᵀ
world-coherent-final-source-ν-catchup-proofᵀ
    source-only
    (source-nu-index safe occ r refl) replacement
    coherent exclusive unique wfL hA h⇑A s↑ liftρ liftγ
    vL noL vV′ noV′ L⊑V′ =
  source-only {{safe = safe}}
    coherent exclusive unique wfL hA h⇑A s↑ liftρ liftγ
    vL noL vV′ noV′ L⊑V′ replacement
