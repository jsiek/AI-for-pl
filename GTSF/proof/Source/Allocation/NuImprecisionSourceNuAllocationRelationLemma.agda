module
  proof.Source.Allocation.NuImprecisionSourceNuAllocationRelationLemma
  where

-- File Charter:
--   * Supplies the canonical source-only `ν` allocation relations.
--   * Keeps callers independent of the implementation module while exposing
--     only the final QTI edges from the contracts.
--   * Contains no postulate, hole, permissive option, or simulation import.

open import proof.Source.Allocation.NuImprecisionSourceNuAllocationRelationDef
  using
  ( SourceInstAllocationRelationᵀ
  ; SourceRevealAllocationRelationᵀ
  )
open import
  proof.Source.Allocation.NuImprecisionSourceNuAllocationRelationProof
  using
  ( source-inst-allocation-relation-proofᵀ
  ; source-reveal-allocation-relation-proofᵀ
  )


source-inst-allocation-relationᵀ :
  SourceInstAllocationRelationᵀ
source-inst-allocation-relationᵀ =
  source-inst-allocation-relation-proofᵀ


source-reveal-allocation-relationᵀ :
  SourceRevealAllocationRelationᵀ
source-reveal-allocation-relationᵀ =
  source-reveal-allocation-relation-proofᵀ
