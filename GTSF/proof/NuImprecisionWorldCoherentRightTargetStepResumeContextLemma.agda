module
  proof.NuImprecisionWorldCoherentRightTargetStepResumeContextLemma
  where

-- File Charter:
--   * Exposes canonical context-preserving active target-step resumption.
--   * Keeps the statement and proof modules separate for low-cost clients.
--   * Contains no additional theorem shape, postulate, hole, permissive
--     option, or broad DGG import.

open import
  proof.NuImprecisionWorldCoherentRightTargetStepResumeContextDef
  using (WorldCoherentRightTargetStepResumeContextᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetStepResumeContextProof
  using (world-coherent-right-target-step-resume-context-proofᵀ)


world-coherent-right-target-step-resume-contextᵀ :
  WorldCoherentRightTargetStepResumeContextᵀ
world-coherent-right-target-step-resume-contextᵀ =
  world-coherent-right-target-step-resume-context-proofᵀ
