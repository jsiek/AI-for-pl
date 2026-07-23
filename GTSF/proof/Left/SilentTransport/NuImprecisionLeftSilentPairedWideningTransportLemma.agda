module proof.Left.SilentTransport.NuImprecisionLeftSilentPairedWideningTransportLemma where

-- File Charter:
--   * Exposes canonical left-silent paired-widening transport.
--   * Keeps the assembled inhabitant separate from the constructor proof.
--   * Imports no paired-conversion or recursive catch-up implementation.

open import
  proof.Left.SilentTransport.NuImprecisionLeftSilentPairedWideningTransportDef using
  (LeftSilentPairedWideningTransportᵀ)
open import
  proof.Left.SilentTransport.NuImprecisionLeftSilentPairedWideningTransportProof using
  (left-silent-paired-widening-transport-proofᵀ)


left-silent-paired-widening-transportᵀ :
  LeftSilentPairedWideningTransportᵀ
left-silent-paired-widening-transportᵀ =
  left-silent-paired-widening-transport-proofᵀ
