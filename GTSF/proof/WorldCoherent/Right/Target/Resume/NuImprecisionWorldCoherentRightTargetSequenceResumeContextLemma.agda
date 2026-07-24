module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeContextLemma
  where

-- File Charter:
--   * Exposes canonical contextual target-sequence resumption.
--   * Keeps callers independent of the private composition implementation.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeContextDef
  using (WorldCoherentRightTargetSequenceResumeContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeContextProof
  using
  (world-coherent-right-target-sequence-resume-context-proofᵀ)


world-coherent-right-target-sequence-resume-contextᵀ :
  WorldCoherentRightTargetSequenceResumeContextᵀ
world-coherent-right-target-sequence-resume-contextᵀ =
  world-coherent-right-target-sequence-resume-context-proofᵀ
