module proof.DGG.Inversion.RightInjInversion2Lemma where

-- File Charter:
--   * Exposes the M3 right-injection inversion theorem.
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
right-inj-inversion² : RightInjInversion²
right-inj-inversion² =
  Proof.right-inj-inversion²
    target-tag-seal-walk target-source-star-chain
