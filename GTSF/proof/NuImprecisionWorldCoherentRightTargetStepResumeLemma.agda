module
  proof.NuImprecisionWorldCoherentRightTargetStepResumeLemma
  where

-- File Charter:
--   * Exposes the canonical active-target-step resumption capability.
--   * Keeps the definition and proof modules separate for low-cost clients.
--   * Contains no additional theorem shape, wrapper hierarchy, postulate,
--     hole, permissive option, or termination bypass.

open import
  proof.NuImprecisionWorldCoherentRightTargetStepResumeDef
  using (WorldCoherentRightTargetStepResumeᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetStepResumeProof
  using (world-coherent-right-target-step-resume-proofᵀ)


world-coherent-right-target-step-resumeᵀ :
  WorldCoherentRightTargetStepResumeᵀ
world-coherent-right-target-step-resumeᵀ =
  world-coherent-right-target-step-resume-proofᵀ
