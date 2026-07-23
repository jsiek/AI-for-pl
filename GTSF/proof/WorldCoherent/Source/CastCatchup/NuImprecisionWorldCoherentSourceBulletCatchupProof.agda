module proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceBulletCatchupProof where

-- File Charter:
--   * Implements coherent source-bullet catch-up as a higher-order adapter.
--   * Reconstructs the allocated bullet relation and delegates recursive
--     value catch-up through its whole statement-level contract.
--   * Contains no recursive dispatcher implementation or permissive holes.

open import QuotientedTermImprecision using (α⊑ᵀ)
open import proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceBulletCatchupDef using
  (WorldCoherentSourceBulletCatchupᵀ)
open import proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef using
  (WorldCoherentLeftValueCatchupPrefixᵀ)


world-coherent-source-bullet-catchup-proofᵀ :
  WorldCoherentLeftValueCatchupPrefixᵀ →
  WorldCoherentSourceBulletCatchupᵀ
world-coherent-source-bullet-catchup-proofᵀ
    catchup h⇑A prefix coherent exclusive wfL okN
    vV′ noV′ vL noL liftρ liftγ L⊑V′ L•⊢ V′⊢ =
  catchup prefix coherent exclusive wfL okN vV′ noV′
    (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑V′ L•⊢ V′⊢)
