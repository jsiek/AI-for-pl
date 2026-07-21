module proof.NuImprecisionWorldCoherentRightSourceFramesLemma where

-- File Charter:
--   * Supplies the canonical right-value source-frame package.
--   * Keeps recursive catch-up assembly independent of the Ginger proof.
--   * Contains no postulate, hole, permissive option, or dispatcher import.

open import proof.NuImprecisionWorldCoherentRightSourceFramesDef using
  (WorldCoherentRightSourceFrames)
open import proof.NuImprecisionWorldCoherentRightSourceFramesProof using
  (world-coherent-right-source-frames-proof)


world-coherent-right-source-frames :
  WorldCoherentRightSourceFrames
world-coherent-right-source-frames =
  world-coherent-right-source-frames-proof
