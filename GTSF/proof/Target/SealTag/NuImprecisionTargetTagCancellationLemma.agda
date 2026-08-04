module proof.Target.SealTag.NuImprecisionTargetTagCancellationLemma where

-- File Charter:
--   * Exposes the canonical target ground-tag cancellation theorem.
--   * Assembles the exact contract from its strict QTI traversal.
--   * Contains no additional theorem shape, result carrier, or simulation
--     dependency.

open import
  proof.Target.SealTag.NuImprecisionTargetTagCancellationDef using
  (TargetTagCancellationᵀ)
open import
  proof.Target.SealTag.NuImprecisionTargetTagCancellationProof using
  (target-tag-cancellation-proofᵀ)


target-tag-cancellationᵀ : TargetTagCancellationᵀ
target-tag-cancellationᵀ = target-tag-cancellation-proofᵀ
