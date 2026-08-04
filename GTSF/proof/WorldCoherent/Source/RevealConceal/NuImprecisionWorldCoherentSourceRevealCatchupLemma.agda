module proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceRevealCatchupLemma where

-- File Charter:
--   * Assembles canonical coherent catch-up through source reveal conversions.
--   * Supplies the completed active-unseal lemma to the strict higher-order
--     reveal proof.
--   * Imports no recursive catch-up dispatcher.

open import proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceRevealCatchupDef using
  (WorldCoherentSourceRevealCatchupᵀ)
open import proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceRevealCatchupProof using
  (world-coherent-source-reveal-catchup-proofᵀ)
open import proof.WorldCoherent.Source.RevealConceal.NuImprecisionWorldCoherentSourceUnsealCatchupLemma using
  (world-coherent-source-unseal-catchupᵀ)


world-coherent-source-reveal-catchupᵀ :
  WorldCoherentSourceRevealCatchupᵀ
world-coherent-source-reveal-catchupᵀ =
  world-coherent-source-reveal-catchup-proofᵀ
    world-coherent-source-unseal-catchupᵀ
