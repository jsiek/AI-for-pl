module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowUntagRootContextLemma
  where

-- File Charter:
--   * Exposes the canonical contextual ordinary target-untag root.
--   * Assembles target-tag cancellation, contextual value terminalization,
--     and contextual target-step resumption.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.Target.SealTag.NuImprecisionTargetTagCancellationLemma using
  (target-tag-cancellationᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowUntagRootContextDef
  using (WorldCoherentRightTargetNarrowUntagRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowUntagRootContextProof
  using (world-coherent-right-target-narrow-untag-root-context-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextLemma
  using (world-coherent-right-target-step-resume-contextᵀ)
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextLemma
  using (world-coherent-right-value-terminal-contextᵀ)


world-coherent-right-target-narrow-untag-root-contextᵀ :
  WorldCoherentRightTargetNarrowUntagRootContextᵀ
world-coherent-right-target-narrow-untag-root-contextᵀ =
  world-coherent-right-target-narrow-untag-root-context-proofᵀ
    target-tag-cancellationᵀ
    world-coherent-right-value-terminal-contextᵀ
    world-coherent-right-target-step-resume-contextᵀ
