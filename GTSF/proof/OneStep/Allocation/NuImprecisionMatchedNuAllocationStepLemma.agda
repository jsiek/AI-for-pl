module
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationStepLemma
  where

-- File Charter:
--   * Supplies the canonical synchronized matched-`ν` allocation step.
--   * Couples its indexed result with fresh-store lineage and keeps clients
--     away from separate raw, transport, and type-coherence operations.
--   * Contains no dispatcher, postulate, hole, permissive option, or legacy
--     allocation-simulation import.

open import
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationStepDef
  using (MatchedNuAllocationStepᵀ)
open import
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationStepProof
  using (matched-nu-allocation-step-proofᵀ)


matched-nu-allocation-stepᵀ : MatchedNuAllocationStepᵀ
matched-nu-allocation-stepᵀ = matched-nu-allocation-step-proofᵀ
