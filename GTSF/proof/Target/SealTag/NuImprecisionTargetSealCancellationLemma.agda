module proof.Target.SealTag.NuImprecisionTargetSealCancellationLemma where

-- File Charter:
--   * Exposes the canonical exact-world target-seal cancellation lemma.
--   * Keeps the public inhabitant separate from its structural proof module.
--   * Imports no live dispatcher or catch-up implementation.

open import proof.Target.SealTag.NuImprecisionTargetSealCancellationDef using
  (TargetSealCancellationᵀ)
open import proof.Target.SealTag.NuImprecisionTargetSealCancellationProof using
  (target-seal-cancellation-proofᵀ)


target-seal-cancellationᵀ : TargetSealCancellationᵀ
target-seal-cancellationᵀ = target-seal-cancellation-proofᵀ
