module
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationAfterValueCatchupLemma
  where

-- File Charter:
--   * Supplies matched allocation after left catch-up reaches a value.
--   * Instantiates the generic composition proof with the canonical indexed
--     matched-allocation result and its fresh-store lineage.
--   * Contains no dispatcher, postulate, hole, permissive option, or legacy
--     allocation-simulation import.

open import
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationAfterValueCatchupDef
  using (MatchedNuAllocationAfterValueCatchupᵀ)
open import
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationAfterValueCatchupProof
  using (matched-nu-allocation-after-value-catchup-proofᵀ)
open import
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationStepLemma
  using (matched-nu-allocation-stepᵀ)


matched-nu-allocation-after-value-catchupᵀ :
  MatchedNuAllocationAfterValueCatchupᵀ
matched-nu-allocation-after-value-catchupᵀ =
  matched-nu-allocation-after-value-catchup-proofᵀ
    matched-nu-allocation-stepᵀ
