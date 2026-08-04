module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowIdentityRootContextLemma
  where

-- File Charter:
--   * Exposes the canonical contextual target-narrowing identity-root leaf.
--   * Supplies the shared contextual identity-root theorem to the strict
--     higher-order narrowing proof.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetIdentityRootContextLemma
  using (world-coherent-right-target-identity-root-contextᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowIdentityRootContextDef
  using (WorldCoherentRightTargetNarrowIdentityRootContextᵀ)
open import
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowIdentityRootContextProof
  using (world-coherent-right-target-narrow-identity-root-context-proofᵀ)


world-coherent-right-target-narrow-identity-root-contextᵀ :
  WorldCoherentRightTargetNarrowIdentityRootContextᵀ
world-coherent-right-target-narrow-identity-root-contextᵀ =
  world-coherent-right-target-narrow-identity-root-context-proofᵀ
    world-coherent-right-target-identity-root-contextᵀ
