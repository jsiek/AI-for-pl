module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootLemma
  where

-- File Charter:
--   * Exposes canonical ordinary target `fun-untag-gen` root resumption.
--   * Supplies ordinary terminal, untag, inert-framing, and step-resumption
--     capabilities to the strict higher-order root proof.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootDef
  using (WorldCoherentRightTargetNarrowFunUntagGenRootᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowFunUntagGenRootProof
  using
  (world-coherent-right-target-narrow-fun-untag-gen-root-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingProof
  using (world-coherent-right-target-inert-framing-proofᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeLemma
  using (world-coherent-right-target-step-resumeᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetNarrowUntagRootLemma
  using (world-coherent-right-target-narrow-untag-rootᵀ)
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalLemma
  using (world-coherent-right-value-terminalᵀ)


world-coherent-right-target-narrow-fun-untag-gen-rootᵀ :
  WorldCoherentRightTargetNarrowFunUntagGenRootᵀ
world-coherent-right-target-narrow-fun-untag-gen-rootᵀ =
  world-coherent-right-target-narrow-fun-untag-gen-root-proofᵀ
    world-coherent-right-value-terminalᵀ
    world-coherent-right-target-narrow-untag-rootᵀ
    world-coherent-right-target-inert-framing-proofᵀ
    world-coherent-right-target-step-resumeᵀ
