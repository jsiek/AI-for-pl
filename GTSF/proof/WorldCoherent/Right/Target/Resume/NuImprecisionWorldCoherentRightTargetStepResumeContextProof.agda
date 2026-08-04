module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextProof
  where

-- File Charter:
--   * Exposes the context-preserving active target-step resumption proof from
--     the implementation module that shares its private composition algebra.
--   * Keeps the canonical statement/proof/lemma dependency direction small.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextDef
  using (WorldCoherentRightTargetStepResumeContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeProof as Resume
  using ()


world-coherent-right-target-step-resume-context-proofᵀ :
  WorldCoherentRightTargetStepResumeContextᵀ
world-coherent-right-target-step-resume-context-proofᵀ =
  Resume.world-coherent-right-target-step-resume-context-proofᵀ
