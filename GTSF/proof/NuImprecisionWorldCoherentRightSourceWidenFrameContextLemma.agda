module
  proof.NuImprecisionWorldCoherentRightSourceWidenFrameContextLemma
  where

-- File Charter:
--   * Exposes canonical contextual source widening framing.
--   * Keeps the statement and proof modules separate for low-cost clients.
--   * Contains no additional theorem shape, postulate, hole, permissive
--     option, or broad DGG import.

open import
  proof.NuImprecisionWorldCoherentRightSourceWidenFrameContextDef
  using (WorldCoherentRightSourceWidenFrameContextᵀ)
open import
  proof.NuImprecisionWorldCoherentRightSourceWidenFrameContextProof
  using (world-coherent-right-source-widen-frame-context-proofᵀ)


world-coherent-right-source-widen-frame-contextᵀ :
  WorldCoherentRightSourceWidenFrameContextᵀ
world-coherent-right-source-widen-frame-contextᵀ =
  world-coherent-right-source-widen-frame-context-proofᵀ
