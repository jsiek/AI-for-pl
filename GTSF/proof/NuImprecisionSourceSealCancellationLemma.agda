module proof.NuImprecisionSourceSealCancellationLemma where

-- File Charter:
--   * Exposes the canonical exact-world source-seal cancellation lemma.
--   * Keeps the public inhabitant separate from its structural proof module.
--   * Imports no live dispatcher or catch-up implementation.

open import proof.NuImprecisionSourceSealCancellationDef using
  (SourceSealCancellationᵀ)
open import proof.NuImprecisionSourceSealCancellationProof using
  (source-seal-cancellation-proofᵀ)


source-seal-cancellationᵀ : SourceSealCancellationᵀ
source-seal-cancellationᵀ = source-seal-cancellation-proofᵀ
