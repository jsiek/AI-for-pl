module proof.DGG.Inversion.TargetWalkLemma where

-- File Charter:
--   * Exposes the checked target tag/seal walk inhabitant.
--   * Keeps consumers independent of the proof-script module name.
--   * Does not expose source-strip internals.

open import proof.DGG.Inversion.TargetWalkProof public using
  (target-tag-seal-walk)

