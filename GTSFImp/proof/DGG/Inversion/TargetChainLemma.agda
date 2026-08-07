module proof.DGG.Inversion.TargetChainLemma where

-- File Charter:
--   * Exposes the checked source-star chain inhabitants at the Def types.
--   * Keeps consumers independent of the proof-script module name.
--   * Does not expose or depend on the target walk proof.

open import proof.DGG.Inversion.TargetChainProof public using
  (target-source-star-at; target-source-star-chain)
