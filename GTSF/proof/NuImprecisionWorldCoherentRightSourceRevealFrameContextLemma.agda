module
  proof.NuImprecisionWorldCoherentRightSourceRevealFrameContextLemma
  where

-- File Charter:
--   * Exposes canonical contextual source reveal framing.
--   * Keeps the statement and proof modules separate for low-cost clients.
--   * Contains no additional theorem shape, postulate, hole, permissive
--     option, or broad DGG import.

open import
  proof.NuImprecisionWorldCoherentRightSourceRevealFrameContextDef
  using (WorldCoherentRightSourceRevealFrameContextᵀ)
open import
  proof.NuImprecisionWorldCoherentRightSourceRevealFrameContextProof
  using (world-coherent-right-source-reveal-frame-context-proofᵀ)


world-coherent-right-source-reveal-frame-contextᵀ :
  WorldCoherentRightSourceRevealFrameContextᵀ
world-coherent-right-source-reveal-frame-contextᵀ =
  world-coherent-right-source-reveal-frame-context-proofᵀ
