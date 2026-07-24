module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootContextLemma
  where

-- File Charter:
--   * Exposes the canonical contextual eager target `fun-untag-gen` root.
--   * Assembles the terminal seed, ordinary function-untag, inert framing,
--     and contextual target-step resumption capabilities.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextLemma
  using (world-coherent-right-value-terminal-contextᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootContextDef
  using (WorldCoherentRightTargetNarrowFunUntagGenRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootContextProof
  using
  (world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowUntagRootContextLemma
  using (world-coherent-right-target-narrow-untag-root-contextᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingContextLemma
  using (world-coherent-right-target-inert-framing-contextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextLemma
  using (world-coherent-right-target-step-resume-contextᵀ)


world-coherent-right-target-narrow-fun-untag-gen-root-contextᵀ :
  WorldCoherentRightTargetNarrowFunUntagGenRootContextᵀ
world-coherent-right-target-narrow-fun-untag-gen-root-contextᵀ =
  world-coherent-right-target-narrow-fun-untag-gen-root-context-proofᵀ
    world-coherent-right-value-terminal-contextᵀ
    world-coherent-right-target-narrow-untag-root-contextᵀ
    world-coherent-right-target-inert-framing-contextᵀ
    world-coherent-right-target-step-resume-contextᵀ
