module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependContextProof
  where

-- File Charter:
--   * Proves that prepending a target `keep` step preserves the right-only
--     imprecision-context action.
--   * Reuses the canonical catch-up prepend worker and its definitionally
--     unchanged final context.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad simulation import.

open import Data.Product using (_,_)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependContextDef
  using (WorldCoherentRightTargetKeepPrependContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependProof
  using (world-coherent-right-target-keep-prepend-proofᵀ)


world-coherent-right-target-keep-prepend-context-proofᵀ :
  WorldCoherentRightTargetKeepPrependContextᵀ
world-coherent-right-target-keep-prepend-context-proofᵀ
    target→ caught context-eq right-prefix =
  world-coherent-right-target-keep-prepend-proofᵀ
      target→ caught ,
  context-eq ,
  right-prefix
