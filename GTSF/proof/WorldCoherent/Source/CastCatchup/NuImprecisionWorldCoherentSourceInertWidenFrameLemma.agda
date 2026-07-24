module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceInertWidenFrameLemma
  where

-- File Charter:
--   * Supplies the canonical inert source-widening frame capability.
--   * Reuses the strict structural framing proof from source widening.

open import
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceInertWidenFrameDef
  using (WorldCoherentSourceInertWidenFrameᵀ)
open import proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupCasesProof using
  (world-coherent-source-inert-widen-castᵀ)


world-coherent-source-inert-widen-frameᵀ :
  WorldCoherentSourceInertWidenFrameᵀ
world-coherent-source-inert-widen-frameᵀ =
  world-coherent-source-inert-widen-castᵀ
