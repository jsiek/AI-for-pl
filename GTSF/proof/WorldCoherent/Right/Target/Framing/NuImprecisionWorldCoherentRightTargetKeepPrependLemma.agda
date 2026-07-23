module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependLemma
  where

-- File Charter:
--   * Exposes the canonical target-only pure-step prepend theorem for
--     world-coherent right-value catch-up.
--   * Keeps callers independent of the worker proof.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad simulation import.

open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependDef
  using (WorldCoherentRightTargetKeepPrependᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependProof
  using (world-coherent-right-target-keep-prepend-proofᵀ)


world-coherent-right-target-keep-prependᵀ :
  WorldCoherentRightTargetKeepPrependᵀ
world-coherent-right-target-keep-prependᵀ =
  world-coherent-right-target-keep-prepend-proofᵀ
