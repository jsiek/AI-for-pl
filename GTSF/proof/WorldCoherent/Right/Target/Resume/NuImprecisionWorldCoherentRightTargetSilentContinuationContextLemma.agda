module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSilentContinuationContextLemma
  where

-- File Charter:
--   * Exposes canonical exact-endpoint continuation for two world-coherent
--     right-value catch-ups.
--   * Keeps the statement and proof modules separate for strict clients.
--   * Contains no additional theorem shape, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSilentContinuationContextDef
  using (WorldCoherentRightTargetSilentContinuationContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSilentContinuationContextProof
  using
  (world-coherent-right-target-silent-continuation-context-proofᵀ)


world-coherent-right-target-silent-continuation-contextᵀ :
  WorldCoherentRightTargetSilentContinuationContextᵀ
world-coherent-right-target-silent-continuation-contextᵀ =
  world-coherent-right-target-silent-continuation-context-proofᵀ
