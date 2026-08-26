module proof.DGG.Inversion.RightInjInversion2Lemma where

-- File Charter:
--   * Exposes the M3 right-injection inversion factory conditional on the
--     pinned occupied non-star source-seal residual.
--   * Instantiates the parameterized proof with the composed target-walk
--     factory and the checked source-star-chain inhabitant.
--   * Re-exports no OpenStrata or SealChain machinery.

open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)
import proof.DGG.Inversion.RightInjInversion2Proof as Proof
open import proof.DGG.Inversion.TargetChainLemma using
  (target-source-star-chain)
open import proof.DGG.Inversion.TargetWalkLemma using
  (target-tag-seal-walk)
open import proof.DGG.Inversion.TargetWalkSupport using
  (OccupiedNonStarSourceSealResidual)

right-inj-inversion² : OccupiedNonStarSourceSealResidual
  → RightInjInversion²
right-inj-inversion² occupied =
  Proof.right-inj-inversion²
    (target-tag-seal-walk occupied) target-source-star-chain
