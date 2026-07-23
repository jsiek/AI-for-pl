module
  proof.NuImprecisionWorldCoherentRightTargetKeepPrependContextLemma
  where

-- File Charter:
--   * Exposes the canonical context-preserving target-`keep` prepend theorem.
--   * Keeps callers independent of the worker proof.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad simulation import.

open import
  proof.NuImprecisionWorldCoherentRightTargetKeepPrependContextDef
  using (WorldCoherentRightTargetKeepPrependContextᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetKeepPrependContextProof
  using (world-coherent-right-target-keep-prepend-context-proofᵀ)


world-coherent-right-target-keep-prepend-contextᵀ :
  WorldCoherentRightTargetKeepPrependContextᵀ
world-coherent-right-target-keep-prepend-contextᵀ =
  world-coherent-right-target-keep-prepend-context-proofᵀ
