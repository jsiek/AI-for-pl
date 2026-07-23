module
  proof.NuImprecisionWorldCoherentRightSourceConcealFrameContextLemma
  where

-- File Charter:
--   * Exposes canonical contextual source conceal framing.
--   * Keeps the statement and proof modules separate for low-cost clients.
--   * Contains no additional theorem shape, postulate, hole, permissive
--     option, or broad DGG import.

open import
  proof.NuImprecisionWorldCoherentRightSourceConcealFrameContextDef
  using (WorldCoherentRightSourceConcealFrameContextᵀ)
open import
  proof.NuImprecisionWorldCoherentRightSourceConcealFrameContextProof
  using (world-coherent-right-source-conceal-frame-context-proofᵀ)


world-coherent-right-source-conceal-frame-contextᵀ :
  WorldCoherentRightSourceConcealFrameContextᵀ
world-coherent-right-source-conceal-frame-contextᵀ =
  world-coherent-right-source-conceal-frame-context-proofᵀ
