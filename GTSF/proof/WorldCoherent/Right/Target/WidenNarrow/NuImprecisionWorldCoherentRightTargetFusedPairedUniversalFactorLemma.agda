module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedPairedUniversalFactorLemma
  where

-- File Charter:
--   * Exposes the canonical fused paired universal factor helper.
--   * Supplies the completed source-only factor used to exclude a source-only
--     origin below a paired ambient final index.
--   * Contains no term relation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedPairedUniversalFactorDef
  using (WorldCoherentRightTargetFusedPairedUniversalFactorᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedPairedUniversalFactorProof
  using
  (world-coherent-right-target-fused-paired-universal-factor-proofᵀ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessLemma
  using (assumption-membership-unique→precision-index-unique)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetFusedSourceOnlyUniversalFactorLemma
  using
  (world-coherent-right-target-fused-source-only-universal-factorᵀ)


world-coherent-right-target-fused-paired-universal-factorᵀ :
  WorldCoherentRightTargetFusedPairedUniversalFactorᵀ
world-coherent-right-target-fused-paired-universal-factorᵀ =
  world-coherent-right-target-fused-paired-universal-factor-proofᵀ
    assumption-membership-unique→precision-index-unique
    world-coherent-right-target-fused-source-only-universal-factorᵀ
