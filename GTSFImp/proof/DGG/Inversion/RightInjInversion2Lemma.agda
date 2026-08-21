module proof.DGG.Inversion.RightInjInversion2Lemma where

-- File Charter:
--   * Exposes the M3 right-injection inversion theorem.
--   * Reuses the direct proof without target-walk or source-star-chain
--     factories.
--   * Re-exports no OpenStrata or SealChain machinery.

open import proof.DGG.Inversion.RightInjInversion2Def using
  (RightInjInversion²)
import proof.DGG.Inversion.RightInjInversion2Proof as Proof
right-inj-inversion² : RightInjInversion²
right-inj-inversion² = Proof.right-inj-inversion²
