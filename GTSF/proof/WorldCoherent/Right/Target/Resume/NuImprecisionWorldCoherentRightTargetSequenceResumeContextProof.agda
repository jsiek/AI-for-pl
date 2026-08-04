module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeContextProof
  where

-- File Charter:
--   * Exposes the contextual target-sequence resumption proof from the
--     implementation module that shares its private composition algebra.
--   * Keeps the statement/proof/lemma dependency direction small.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeContextDef
  using (WorldCoherentRightTargetSequenceResumeContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeProof
  as Resume
  using ()


world-coherent-right-target-sequence-resume-context-proofᵀ :
  WorldCoherentRightTargetSequenceResumeContextᵀ
world-coherent-right-target-sequence-resume-context-proofᵀ =
  Resume.world-coherent-right-target-sequence-resume-context-proofᵀ
