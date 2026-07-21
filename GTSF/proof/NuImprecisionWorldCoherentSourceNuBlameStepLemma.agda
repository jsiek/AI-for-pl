module proof.NuImprecisionWorldCoherentSourceNuBlameStepLemma where

-- File Charter:
--   * Supplies the canonical source `ν`-blame step capability.
--   * Keeps source one-step assembly independent of the Ginger proof module.
--   * Contains no postulate, hole, permissive option, or dispatcher import.

open import proof.NuImprecisionWorldCoherentSourceNuBlameStepDef using
  (WorldCoherentSourceNuBlameStepᵀ)
open import proof.NuImprecisionWorldCoherentSourceNuBlameStepProof using
  (world-coherent-source-ν-blame-step-proofᵀ)


world-coherent-source-ν-blame-stepᵀ :
  WorldCoherentSourceNuBlameStepᵀ
world-coherent-source-ν-blame-stepᵀ =
  world-coherent-source-ν-blame-step-proofᵀ
