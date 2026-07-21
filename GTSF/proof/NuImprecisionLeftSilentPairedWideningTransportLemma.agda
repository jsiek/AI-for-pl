module proof.NuImprecisionLeftSilentPairedWideningTransportLemma where

-- File Charter:
--   * Exposes canonical left-silent paired-widening transport.
--   * Keeps the assembled inhabitant separate from the constructor proof.
--   * Imports no paired-conversion or recursive catch-up implementation.

open import
  proof.NuImprecisionLeftSilentPairedWideningTransportDef using
  (LeftSilentPairedWideningTransportᵀ)
open import
  proof.NuImprecisionLeftSilentPairedWideningTransportProof using
  (left-silent-paired-widening-transport-proofᵀ)


left-silent-paired-widening-transportᵀ :
  LeftSilentPairedWideningTransportᵀ
left-silent-paired-widening-transportᵀ =
  left-silent-paired-widening-transport-proofᵀ
