module proof.Source.SealTag.NuImprecisionSourceTagCancellationLemma where

-- File Charter:
--   * Assembles source ground-tag cancellation from its proof module.
--   * Supplies the canonical ground-value quotient-elimination dependency.
--   * Exposes the canonical inhabitant of the separately stated theorem.

open import
  proof.Target.GroundValue.NuImprecisionGroundValueQuotientEliminationLemma using
  (ground-value-quotient-eliminationᵀ)
open import proof.Source.SealTag.NuImprecisionSourceTagCancellationDef using
  (SourceTagCancellationᵀ)
open import proof.Source.SealTag.NuImprecisionSourceTagCancellationProof using
  (source-tag-cancellation-proofᵀ)


source-tag-cancellationᵀ : SourceTagCancellationᵀ
source-tag-cancellationᵀ =
  source-tag-cancellation-proofᵀ
    ground-value-quotient-eliminationᵀ
