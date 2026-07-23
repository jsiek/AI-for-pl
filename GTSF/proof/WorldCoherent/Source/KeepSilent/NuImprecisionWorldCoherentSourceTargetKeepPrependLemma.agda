module
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependLemma
  where

-- File Charter:
--   * Exposes the canonical target-only pure-step prepend capability.
--   * Keeps downstream modules independent of its implementation imports.
--   * Contains no implementation, postulate, hole, or permissive option.

open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependDef
  using (WorldCoherentSourceTargetKeepPrependᵀ)
open import
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceTargetKeepPrependProof
  using (world-coherent-source-target-keep-prepend-proofᵀ)


world-coherent-source-target-keep-prependᵀ :
  WorldCoherentSourceTargetKeepPrependᵀ
world-coherent-source-target-keep-prependᵀ =
  world-coherent-source-target-keep-prepend-proofᵀ
