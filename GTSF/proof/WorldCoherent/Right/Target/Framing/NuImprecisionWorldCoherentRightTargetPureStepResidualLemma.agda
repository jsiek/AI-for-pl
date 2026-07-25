module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetPureStepResidualLemma
  where

-- File Charter:
--   * Exposes canonical pure target-step residualization.
--   * Contains no implementation, recursion, postulate, hole, or permissive
--     option.

open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetPureStepResidualDef
  using (WorldCoherentRightTargetPureStepResidualᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetPureStepResidualProof
  using (world-coherent-right-target-pure-step-residual-proofᵀ)


world-coherent-right-target-pure-step-residualᵀ :
  WorldCoherentRightTargetPureStepResidualᵀ
world-coherent-right-target-pure-step-residualᵀ =
  world-coherent-right-target-pure-step-residual-proofᵀ
