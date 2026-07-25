module proof.Right.Core.NuImprecisionPairedCastTransportLemma where

-- File Charter:
--   * Exposes the canonical paired-cast transport theorem for arbitrary
--     weak one-step results, including an allocating leading step.
--   * Keeps consumers independent of the right-silent compatibility
--     specialization that shares the implementation.
--   * Contains no wrapper relation, postulate, hole, permissive option, or
--     implementation detail.

open import proof.Right.Core.NuImprecisionPairedCastTransportDef using
  (PairedCastTransportᵀ)
open import proof.Right.Core.NuImprecisionRightSilentPairedCastTransportProof
  using (paired-cast-transport-proofᵀ)


paired-cast-transportᵀ :
  PairedCastTransportᵀ
paired-cast-transportᵀ =
  paired-cast-transport-proofᵀ
