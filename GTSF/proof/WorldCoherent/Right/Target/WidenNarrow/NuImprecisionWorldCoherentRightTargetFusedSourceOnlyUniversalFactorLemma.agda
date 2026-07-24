module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedSourceOnlyUniversalFactorLemma
  where

-- File Charter:
--   * Exposes the canonical fused source-only universal factor helper.
--   * Keeps callers independent of its exhaustive origin-type inversion.
--   * Contains no term relation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedSourceOnlyUniversalFactorDef
  using (WorldCoherentRightTargetFusedSourceOnlyUniversalFactorᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedSourceOnlyUniversalFactorProof
  using
  (world-coherent-right-target-fused-source-only-universal-factor-proofᵀ)


world-coherent-right-target-fused-source-only-universal-factorᵀ :
  WorldCoherentRightTargetFusedSourceOnlyUniversalFactorᵀ
world-coherent-right-target-fused-source-only-universal-factorᵀ =
  world-coherent-right-target-fused-source-only-universal-factor-proofᵀ
