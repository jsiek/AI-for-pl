module
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletProof
  where

-- File Charter:
--   * Proves the target-bullet lambda-beta scheduling leaf from the canonical
--     source-application/target-bullet exclusion.
--   * Separates general target-bullet reachability from this impossible
--     source application shape.
--   * Contains no catch-all, postulate, hole, or permissive option.

open import Data.Empty using (⊥-elim)

open import
  proof.NuImprecisionTargetBulletSourceApplicationExclusionLemma
  using (quotiented-target-bullet-excludes-source-applicationᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceLambdaBetaTargetBulletDef
  using (WorldCoherentSourceLambdaBetaTargetBulletᵀ)


world-coherent-source-lambda-beta-target-bullet-proofᵀ :
  WorldCoherentSourceLambdaBetaTargetBulletᵀ
world-coherent-source-lambda-beta-target-bullet-proofᵀ
    prefix coherent exclusive unique wfL wfR okM okM′ M⊢ M′⊢
    relation vV =
  ⊥-elim
    (quotiented-target-bullet-excludes-source-applicationᵀ relation)
