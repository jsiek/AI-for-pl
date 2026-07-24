module
  proof.Target.Administration.NuImprecisionTargetUniversalFusionSpineLemma
  where

-- File Charter:
--   * Exposes the canonical fold from universal target-instantiation fusion
--     spines to quotiented term imprecision.
--   * Supplies only the completed strict proof and introduces no wrapper,
--     extraction, normalization, postulate, hole, permissive option, or
--     broad DGG import.

open import
  proof.Target.Administration.NuImprecisionTargetUniversalFusionSpineDef
  using (TargetUniversalFusionSpineRelationᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetUniversalFusionSpineProof
  using (target-universal-fusion-spine-relation-proofᵀ)


target-universal-fusion-spine-relationᵀ :
  TargetUniversalFusionSpineRelationᵀ
target-universal-fusion-spine-relationᵀ =
  target-universal-fusion-spine-relation-proofᵀ
