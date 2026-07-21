module proof.NuImprecisionSourceTagCancellationLemma where

-- File Charter:
--   * Assembles source ground-tag cancellation from its proof module.
--   * Supplies the canonical ground-value quotient-elimination dependency.
--   * Exposes the canonical inhabitant of the separately stated theorem.

open import
  proof.NuImprecisionGroundValueQuotientEliminationLemma using
  (ground-value-quotient-eliminationᵀ)
open import proof.NuImprecisionSourceTagCancellationDef using
  (SourceTagCancellationᵀ)
open import proof.NuImprecisionSourceTagCancellationProof using
  (source-tag-cancellation-proofᵀ)


source-tag-cancellationᵀ : SourceTagCancellationᵀ
source-tag-cancellationᵀ =
  source-tag-cancellation-proofᵀ
    ground-value-quotient-eliminationᵀ
