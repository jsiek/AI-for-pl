module
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllResidualCasesDef
  where

-- File Charter:
--   * Collects the five residual semantic capabilities needed by
--     source-universal right-value closing.
--   * Each major lemma statement lives in its own canonical `Def` file for
--     independent proof and checking.
--   * This is a flat capability record, not a result, view, outcome, or
--     recursive-plan hierarchy.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, compatibility re-export, or broad simulation import.

open import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllNestedSourceAllDef
  using (WorldCoherentRightSourceAllNestedSourceAllᵀ)
open import
  proof.Right.SourceAll.Frames.NuImprecisionRightSourceAllPairedCastDef
  using (WorldCoherentRightSourceAllPairedCastᵀ)
open import
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllQuotientDef
  using (WorldCoherentRightSourceAllQuotientᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetAllocationDef
  using (WorldCoherentRightSourceAllTargetAllocationᵀ)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetBulletDef
  using (WorldCoherentRightSourceAllTargetBulletᵀ)


record WorldCoherentRightSourceAllResidualCases : Set₁ where
  field
    sourceAllPairedCast :
      WorldCoherentRightSourceAllPairedCastᵀ
    sourceAllQuotient :
      WorldCoherentRightSourceAllQuotientᵀ
    sourceAllNestedSourceAll :
      WorldCoherentRightSourceAllNestedSourceAllᵀ
    sourceAllTargetBullet :
      WorldCoherentRightSourceAllTargetBulletᵀ
    sourceAllTargetAllocation :
      WorldCoherentRightSourceAllTargetAllocationᵀ

open WorldCoherentRightSourceAllResidualCases public
