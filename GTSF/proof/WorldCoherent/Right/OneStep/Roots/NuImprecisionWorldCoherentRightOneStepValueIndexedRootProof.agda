module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepValueIndexedRootProof
  where

-- File Charter:
--   * Proves the generic source-value target indexed-step root by completing
--     right-value catch-up and consuming the observed target step.
--   * Projects the residual weak result, lineage, and final-world invariants
--     into the ordinary one-step outcome.
--   * Contains no recursion, dispatcher, postulate, hole, permissive option,
--     compatibility alias, or dependency wrapper.

open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (world-indexed-outcome-related)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepValueIndexedRootDef
  using (WorldCoherentRightOneStepValueIndexedRootᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualDef
  using
  ( WorldCoherentRightTargetIndexedStepResidualᵀ
  ; world-coherent-right-target-indexed-step-residual
  )
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)


world-coherent-right-one-step-value-indexed-root-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentRightTargetIndexedStepResidualᵀ →
  WorldCoherentRightOneStepValueIndexedRootᵀ
world-coherent-right-one-step-value-indexed-root-proofᵀ
    catchup residual prefix coherent exclusive unique wfR okM′
    vV noV V⊑M′ target-step
    with residual target-step
      (catchup prefix coherent exclusive unique wfR
        okM′ vV noV V⊑M′)
world-coherent-right-one-step-value-indexed-root-proofᵀ
    catchup residual prefix coherent exclusive unique wfR okM′
    vV noV V⊑M′ target-step
    | world-coherent-right-target-indexed-step-residual
        caught source-empty source-unchanged source-value source-no
        target-value target-no lineage bullet runtime-transport
        final-coherent final-exclusive final-unique final-wfR =
  world-indexed-outcome-related
    caught lineage final-coherent final-exclusive final-unique
