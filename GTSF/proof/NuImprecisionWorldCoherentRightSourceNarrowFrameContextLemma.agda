module
  proof.NuImprecisionWorldCoherentRightSourceNarrowFrameContextLemma
  where

-- File Charter:
--   * Exposes canonical contextual source narrowing framing.
--   * Keeps the statement and proof modules separate for low-cost clients.
--   * Contains no additional theorem shape, postulate, hole, permissive
--     option, or broad DGG import.

open import
  proof.NuImprecisionWorldCoherentRightSourceNarrowFrameContextDef
  using (WorldCoherentRightSourceNarrowFrameContextᵀ)
open import
  proof.NuImprecisionWorldCoherentRightSourceNarrowFrameContextProof
  using
  (world-coherent-right-source-narrow-frame-context-proofᵀ)


world-coherent-right-source-narrow-frame-contextᵀ :
  WorldCoherentRightSourceNarrowFrameContextᵀ
world-coherent-right-source-narrow-frame-contextᵀ =
  world-coherent-right-source-narrow-frame-context-proofᵀ
