module proof.NuImprecisionWorldCoherentSourceRevealCatchupLemma where

-- File Charter:
--   * Assembles canonical coherent catch-up through source reveal conversions.
--   * Supplies the completed active-unseal lemma to the strict higher-order
--     reveal proof.
--   * Imports no recursive catch-up dispatcher.

open import proof.NuImprecisionWorldCoherentSourceRevealCatchupDef using
  (WorldCoherentSourceRevealCatchupᵀ)
open import proof.NuImprecisionWorldCoherentSourceRevealCatchupProof using
  (world-coherent-source-reveal-catchup-proofᵀ)
open import proof.NuImprecisionWorldCoherentSourceUnsealCatchupLemma using
  (world-coherent-source-unseal-catchupᵀ)


world-coherent-source-reveal-catchupᵀ :
  WorldCoherentSourceRevealCatchupᵀ
world-coherent-source-reveal-catchupᵀ =
  world-coherent-source-reveal-catchup-proofᵀ
    world-coherent-source-unseal-catchupᵀ
