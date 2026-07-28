module
  proof.OneStep.RuntimeBullet.NuImprecisionMatchedBetaGenNarrowingLemma
  where

-- File Charter:
--   * Supplies the canonical matched post-allocation `β-gen•` narrowing
--     relation.
--   * Instantiates generic allocation transport while leaving both operational
--     reduction steps to their simulation consumers.
--   * Contains no dispatcher, postulate, hole, permissive option, wrapper
--     re-export, or legacy allocation-simulation import.

open import proof.Core.Properties.NarrowWidenProperties using
  (allocate-gen-narrowing)
open import
  proof.OneStep.RuntimeBullet.NuImprecisionMatchedBetaGenNarrowingDef
  using (MatchedPostAllocationBetaGenNarrowingRelationᵀ)
open import
  proof.OneStep.RuntimeBullet.NuImprecisionMatchedBetaGenNarrowingProof
  using (matched-post-allocation-β-gen-narrowing-relation-proofᵀ)


matched-post-allocation-β-gen-narrowing-relationᵀ :
  MatchedPostAllocationBetaGenNarrowingRelationᵀ
matched-post-allocation-β-gen-narrowing-relationᵀ =
  matched-post-allocation-β-gen-narrowing-relation-proofᵀ
    allocate-gen-narrowing
