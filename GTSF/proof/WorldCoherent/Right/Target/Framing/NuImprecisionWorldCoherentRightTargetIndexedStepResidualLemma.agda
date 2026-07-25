module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualLemma
  where

-- File Charter:
--   * Exposes canonical indexed target-step residualization.
--   * Contains no implementation, dispatcher, recursion, postulate, hole,
--     permissive option, compatibility alias, or dependency wrapper.

open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualDef
  using (WorldCoherentRightTargetIndexedStepResidualᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualProof
  using (world-coherent-right-target-indexed-step-residual-proofᵀ)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)


world-coherent-right-target-indexed-step-residualᵀ :
  WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ →
  WorldCoherentRightTargetIndexedStepResidualᵀ
world-coherent-right-target-indexed-step-residualᵀ runtime-transport =
  world-coherent-right-target-indexed-step-residual-proofᵀ
    runtime-transport
