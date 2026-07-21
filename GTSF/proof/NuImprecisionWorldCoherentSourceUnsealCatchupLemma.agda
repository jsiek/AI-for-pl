module proof.NuImprecisionWorldCoherentSourceUnsealCatchupLemma where

-- File Charter:
--   * Assembles canonical coherent catch-up through active source unseal.
--   * Supplies the repaired source-seal cancellation lemma to the strict
--     higher-order proof.
--   * Imports no recursive catch-up dispatcher.

open import proof.NuImprecisionSourceSealCancellationLemma using
  (source-seal-cancellationᵀ)
open import proof.NuImprecisionWorldCoherentSourceUnsealCatchupDef using
  (WorldCoherentSourceUnsealCatchupᵀ)
open import proof.NuImprecisionWorldCoherentSourceUnsealCatchupProof using
  (world-coherent-source-unseal-catchup-proofᵀ)


world-coherent-source-unseal-catchupᵀ :
  WorldCoherentSourceUnsealCatchupᵀ
world-coherent-source-unseal-catchupᵀ =
  world-coherent-source-unseal-catchup-proofᵀ
    source-seal-cancellationᵀ
