module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetIdentityRootContextLemma
  where

-- File Charter:
--   * Exposes the canonical contextual target identity-root theorem.
--   * Keeps clients independent of the active-root proof implementation.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetIdentityRootContextDef
  using (WorldCoherentRightTargetIdentityRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetIdentityRootContextProof
  using (world-coherent-right-target-identity-root-context-proofᵀ)
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextLemma
  using (world-coherent-right-value-terminal-contextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextLemma
  using (world-coherent-right-target-step-resume-contextᵀ)


world-coherent-right-target-identity-root-contextᵀ :
  WorldCoherentRightTargetIdentityRootContextᵀ
world-coherent-right-target-identity-root-contextᵀ =
  world-coherent-right-target-identity-root-context-proofᵀ
    world-coherent-right-value-terminal-contextᵀ
    world-coherent-right-target-step-resume-contextᵀ
