module proof.NuImprecisionSourceCastSequenceMidpointLemma where

-- File Charter:
--   * Exposes the canonical source cast-sequence midpoint capability.
--   * Keeps the assembled inhabitant separate from its structural proof.
--   * Imports no recursive catch-up implementation.

open import proof.NuImprecisionSourceCastSequenceMidpointDef using
  (SourceCastSequenceMidpointᵀ)
open import proof.NuImprecisionSourceCastSequenceMidpointProof using
  (source-cast-sequence-midpoint-proofᵀ)


source-cast-sequence-midpointᵀ : SourceCastSequenceMidpointᵀ
source-cast-sequence-midpointᵀ = source-cast-sequence-midpoint-proofᵀ
