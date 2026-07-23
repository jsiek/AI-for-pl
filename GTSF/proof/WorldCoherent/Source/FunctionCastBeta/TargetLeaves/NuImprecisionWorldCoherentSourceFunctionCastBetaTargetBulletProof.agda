module
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletProof
  where

-- File Charter:
--   * Proves the source function-cast beta target-bullet leaf from the
--     canonical source-application/target-bullet exclusion.
--   * Contains no catch-all, postulate, hole, or permissive option.

open import Data.Empty using (⊥-elim)

open import
  proof.Target.Core.NuImprecisionTargetBulletSourceApplicationExclusionLemma
  using (quotiented-target-bullet-excludes-source-applicationᵀ)
open import
  proof.WorldCoherent.Source.FunctionCastBeta.TargetLeaves.NuImprecisionWorldCoherentSourceFunctionCastBetaTargetBulletDef
  using (WorldCoherentSourceFunctionCastBetaTargetBulletᵀ)


world-coherent-source-function-cast-beta-target-bullet-proofᵀ :
  WorldCoherentSourceFunctionCastBetaTargetBulletᵀ
world-coherent-source-function-cast-beta-target-bullet-proofᵀ
    prefix coherent exclusive unique wfL wfR okM okM′ M⊢ M′⊢
    relation vV vW =
  ⊥-elim
    (quotiented-target-bullet-excludes-source-applicationᵀ relation)
